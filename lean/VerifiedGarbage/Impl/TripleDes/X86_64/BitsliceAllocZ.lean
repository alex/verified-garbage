import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Register allocation of the DES S-box circuits on AVX-512 registers

Compiles a circuit (`Bitslice.Gate`s, applied to 512-bit words) to AVX-512
instructions on `zmm` registers. First, gates are fused (`fuse`): a gate
whose result is used only once, by another gate, and is no output, is
absorbed into it when the two together have at most three inputs, so that
each remaining gate is one function of up to three words. The functions of
two words that AVX-512 has (`vpxord`, `vpandq`, `vporq`, `vpandnq`) are
those instructions; every other is `vpternlogd`, whose destination is also
its first input: an input that dies there, or else a copy of one. Values
spill to 64-byte slots `[rcx + 64k]` of the scratch buffer when the
registers run out (Belady), and are loaded back before their next use.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

namespace VG.Impl.TripleDes.X86_64.BitsliceAvx512

open VG.X86_64 VG.Impl.TripleDes.Bitslice

/-- Spill slot `k`, 64 bytes in the scratch buffer. -/
def spillAt (k : Nat) : MemOp := { base := .rcx, disp := ((64 * k : Nat) : Int) }

def zbin (op : ZBinOp) (d a b : XReg) : Instr := .zop (.zbin op d a b)

/-! ## Fusing gates into functions of up to three words -/

/-- A function of the variables `ins` (at most three): bit `r` of `table` is
its value when bit `p` of `r` is the value of `ins[p]`. -/
structure Fn where
  ins : List Nat
  table : Nat
  deriving Repr, Inhabited

/-- A fused gate: `dst := f ins`. -/
structure TGate where
  dst : Nat
  f : Fn
  deriving Repr, Inhabited

/-- The row of `ins'` (a sublist of the variables of row `r` of `ins`). -/
def project (ins ins' : List Nat) (r : Nat) : Nat :=
  (List.range ins'.length).foldl (fun acc p =>
    let v := ins'.getD p 0
    let bit := match ins.idxOf? v with | some i => r.testBit i | none => false
    if bit then acc ||| 2 ^ p else acc) 0

def Fn.eval (f : Fn) (ins : List Nat) (r : Nat) : Bool := f.table.testBit (project ins f.ins r)

def opEval : Op → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .xor, a, b => a ^^ b
  | .andn, a, b => a && !b
  | .not, a, _ => !a

/-- The variables a gate reads. -/
def gateIns (g : Gate) : List Nat := if g.op = .not then [g.a] else if g.a = g.b then [g.a] else [g.a, g.b]

/-- `xs` sorted by `key`, stably (structural, so that the kernel evaluates it). -/
def sortBy (key : Nat → Nat) : List Nat → List Nat
  | [] => []
  | x :: xs =>
    let ys := sortBy key xs
    (ys.filter fun y => key y < key x) ++ x :: ys.filter fun y => key x ≤ key y

/-- How many gates read each variable, plus one for each output. -/
def uses (gs : List Gate) (outs : List Nat) (v : Nat) : Nat :=
  (gs.filter fun g => (gateIns g).contains v).length + (outs.filter (· == v)).length

/-- Fuse the gates: each gate's function, and the gates absorbed into others. -/
def fuseAll (gs : List Gate) (outs : List Nat) : List (Nat × Fn) × List Nat :=
  gs.foldl (fun (acc : List (Nat × Fn) × List Nat) g =>
    let (fns, absorbed) := acc
    let fnOf (v : Nat) : Option Fn := (fns.find? (·.1 == v)).map (·.2)
    -- the operands that may be absorbed, smallest first
    let cands := sortBy (fun v => ((fnOf v).map (·.ins.length)).getD 0)
      ((gateIns g).filter fun v => (fnOf v).isSome && uses gs outs v == 1)
    let (leaves, chosen) := cands.foldl (fun (lc : List Nat × List Nat) v =>
      let (leaves, chosen) := lc
      let new := (leaves.filter (· != v)) ++ (((fnOf v).map (·.ins)).getD []).filter
        (fun u => !(leaves.filter (· != v)).contains u)
      if new.length ≤ 3 then (new, v :: chosen) else (leaves, chosen)) (gateIns g, [])
    -- the value of an operand on a row of `leaves`
    let val (v : Nat) (r : Nat) : Bool :=
      if chosen.contains v then
        match fnOf v with
        | some f => f.eval leaves r
        | none => false
      else match leaves.idxOf? v with
        | some i => r.testBit i
        | none => false
    let table := (List.range (2 ^ leaves.length)).foldl (fun t r =>
      if opEval g.op (val g.a r) (val g.b r) then t ||| 2 ^ r else t) 0
    ((g.dst, ⟨leaves, table⟩) :: fns, chosen ++ absorbed)) ([], [])

/-- The fused gates, in order. -/
def fuse (gs : List Gate) (outs : List Nat) : List TGate :=
  let (fns, absorbed) := fuseAll gs outs
  (gs.filter fun g => !absorbed.contains g.dst).map fun g =>
    ⟨g.dst, ((fns.find? (·.1 == g.dst)).map (·.2)).getD ⟨[], 0⟩⟩

/-! ## Allocation -/

/-- The allocation state. -/
structure Alloc where
  regs : List (XReg × Nat)
  slots : List (Nat × Nat)
  free : List XReg
  freeSlots : List Nat
  code : List Instr

namespace Alloc

def regOf (a : Alloc) (v : Nat) : Option XReg := (a.regs.find? (·.2 == v)).map (·.1)

def slotOf (a : Alloc) (v : Nat) : Option Nat := (a.slots.find? (·.2 == v)).map (·.1)

def usesVar (v : Nat) (g : TGate) : Bool := g.f.ins.contains v

def live (rest : List TGate) (outs : List Nat) (v : Nat) : Bool :=
  outs.contains v || rest.any (usesVar v)

def nextUse (rest : List TGate) (outs : List Nat) (v : Nat) : Nat :=
  match rest.findIdx? (usesVar v) with
  | some i => i
  | none => if outs.contains v then rest.length else rest.length + 1

def kill (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    free := match a.regOf v with | some r => r :: a.free | none => a.free
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with | some k => k :: a.freeSlots | none => a.freeSlots }

def evict (a : Alloc) (r : XReg) (v : Nat) : Alloc :=
  let a := { a with regs := a.regs.filter (·.1 != r) }
  match a.slotOf v with
  | some _ => a
  | none => match a.freeSlots with
    | k :: ks =>
      { a with slots := (k, v) :: a.slots, freeSlots := ks,
               code := .vmovdqu32Store (spillAt k) r :: a.code }
    | [] => a

def getReg (a : Alloc) (rest : List TGate) (outs keep : List Nat) : Alloc × XReg :=
  match a.free with
  | r :: rs => ({ a with free := rs }, r)
  | [] =>
    let cands := a.regs.filter fun p => !keep.contains p.2
    let best := cands.foldl (fun (b : Option (XReg × Nat)) p =>
      match b with
      | none => some p
      | some q => if nextUse rest outs p.2 > nextUse rest outs q.2 then some p else some q) none
    match best with
    | some (r, v) => (evict a r v, r)
    | none => (a, .xmm0)

def emit (a : Alloc) (is : List Instr) : Alloc := { a with code := is.reverse ++ a.code }

def inReg (a : Alloc) (rest : List TGate) (outs keep : List Nat) (v : Nat) : Alloc × XReg :=
  match a.regOf v with
  | some r => (a, r)
  | none =>
    let (a, r) := getReg a rest outs keep
    let a := match a.slotOf v with
      | some k => emit a [.vmovdqu32Load r (spillAt k)]
      | none => a
    ({ a with regs := (r, v) :: a.regs }, r)

/-- The registers of the variables `vs`, loading them as needed. -/
def inRegs (a : Alloc) (rest : List TGate) (outs keep : List Nat) : List Nat → Alloc × List XReg
  | [] => (a, [])
  | v :: vs =>
    let (a, r) := inReg a rest outs keep v
    let (a, rs) := inRegs a rest outs keep vs
    (a, r :: rs)

/-- The 8-bit table of `f` for `vpternlogd dst, src1, src2` with the
inputs `x` and `y` there and the third in `src2` (row `4 a + 2 b + c`). -/
def ternImm (f : Fn) (x y : Nat) : BitVec 8 :=
  BitVec.ofNat 8 ((List.range 8).foldl (fun t r =>
    let row := (List.range f.ins.length).foldl (fun acc p =>
      let v := f.ins.getD p 0
      let bit := if v = x then r.testBit 2 else if v = y then r.testBit 1 else r.testBit 0
      if bit then acc ||| 2 ^ p else acc) 0
    if f.table.testBit row then t ||| 2 ^ r else t) 0)

/-- The instruction for a function of two words that AVX-512 has. -/
def binOf (f : Fn) (d a b : XReg) : Option Instr :=
  if f.ins.length != 2 then none else
  match f.table with
  | 6 => some (zbin .vpxord d a b)
  | 8 => some (zbin .vpandq d a b)
  | 14 => some (zbin .vporq d a b)
  | 2 => some (zbin .vpandnq d b a)   -- ins[0] ∧ ¬ins[1]
  | 4 => some (zbin .vpandnq d a b)   -- ¬ins[0] ∧ ins[1]
  | _ => none

def gate (outs : List Nat) (a : Alloc) (g : TGate) (rest : List TGate) : Alloc :=
  let ins := g.f.ins
  let (a, rs) := inRegs a (g :: rest) outs ins ins
  let dead := ins.filter fun v => !live rest outs v
  let a := dead.foldl kill a
  match binOf g.f (rs.getD 0 .xmm0) (rs.getD 0 .xmm0) (rs.getD 1 .xmm0) with
  | some _ =>
    let (a, d) := getReg a rest outs ins
    let i := (binOf g.f d (rs.getD 0 .xmm0) (rs.getD 1 .xmm0)).getD (zbin .vpxord d d d)
    let a := emit a [i]
    { a with regs := (d, g.dst) :: a.regs, free := a.free.filter (· != d) }
  | none =>
    -- the destination: an input that dies here, or a copy of the first
    let x := (ins.find? fun v => dead.contains v).getD (ins.getD 0 0)
    let others := ins.filter (· != x)
    let y := others.getD 0 x
    let z := others.getD 1 y
    let rx := rs.getD (ins.idxOf x) .xmm0
    let ry := rs.getD (ins.idxOf y) rx
    let rz := rs.getD (ins.idxOf z) ry
    let imm := ternImm g.f x y
    if dead.contains x then
      -- `x`'s register is free now: take it back
      let a := { a with free := a.free.filter (· != rx) }
      let a := emit a [.zop (.vpternlogd rx ry rz imm)]
      { a with regs := (rx, g.dst) :: a.regs }
    else
      let (a, d) := getReg a rest outs ins
      let a := emit a [.zop (.vmovdqa64 d rx), .zop (.vpternlogd d ry rz imm)]
      { a with regs := (d, g.dst) :: a.regs, free := a.free.filter (· != d) }

def gates (outs : List Nat) : Alloc → List TGate → Alloc
  | a, [] => a
  | a, g :: gs => gates outs (gate outs a g gs) gs

def place (a : Alloc) : List (Nat × XReg) → Alloc
  | [] => a
  | (v, r) :: outs =>
    if a.regOf v = some r then place a outs else
    let a := match a.regs.find? (·.1 == r) with
      | some (_, u) => evict a r u
      | none => { a with free := a.free.filter (· != r) }
    let a := match a.regOf v with
      | some r' => emit a [.zop (.vmovdqa64 r r')]
      | none => match a.slotOf v with
        | some k => emit a [.vmovdqu32Load r (spillAt k)]
        | none => a
    let a := { a with regs := (r, v) :: a.regs.filter (·.2 != v) }
    place a outs

end Alloc

/-- The code of a circuit whose inputs `ins` start in their registers, the
registers `free` being free, leaving the outputs `outs` in their registers,
spilling to the slots `spill` of the scratch buffer. -/
def compile (gs : List Gate) (ins outs : List (Nat × XReg)) (free : List XReg)
    (spill : List Nat) : List Instr :=
  let init : Alloc :=
    { regs := ins.map (fun (v, r) => (r, v)), slots := [], free := free, freeSlots := spill, code := [] }
  let a := Alloc.gates (outs.map (·.1)) init (fuse gs (outs.map (·.1)))
  let a := Alloc.place a outs
  a.code.reverse

end VG.Impl.TripleDes.X86_64.BitsliceAvx512
