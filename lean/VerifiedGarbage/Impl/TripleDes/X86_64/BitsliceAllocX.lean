import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Register allocation of the DES S-box circuits on SSE registers

Compiles a circuit (`Bitslice.Gate`s, applied to 128-bit words) to
two-operand SSE2 instructions, with the words in `xmm` registers and,
when the registers run out, in 16-byte slots `[rcx + 16k]` of the scratch
buffer. A gate is computed in place of an operand that dies there, or else
in a copy (`movdqa`) of one: `a ∧ ¬b` is `pandn` in place of `b`, or
`(a ∨ b) ⊕ b` in place of `a`; `¬a` is `a ⊕ ones`, `ones` being a register
that holds all ones. When
no register is free, the value whose next use is farthest away (Belady) is
evicted, and spilled to a slot unless it is already in one; a value in a
slot is loaded back into a register before its next use.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

namespace VG.Impl.TripleDes.X86_64.BitsliceSse

open VG.X86_64 VG.Impl.TripleDes.Bitslice

/-- Spill slot `k`, 16 bytes in the scratch buffer. -/
def spillAt (k : Nat) : MemOp := { base := .rcx, disp := ((16 * k : Nat) : Int) }

def xbin (op : XBinOp) (d s : XReg) : Instr := .xop (.bin op d s)

/-- The allocation state. -/
structure Alloc where
  /-- The variable each register holds. -/
  regs : List (XReg × Nat)
  /-- The variable each slot holds. -/
  slots : List (Nat × Nat)
  free : List XReg
  freeSlots : List Nat
  /-- The instructions so far, most recent first. -/
  code : List Instr

namespace Alloc

def regOf (a : Alloc) (v : Nat) : Option XReg := (a.regs.find? (·.2 == v)).map (·.1)

def slotOf (a : Alloc) (v : Nat) : Option Nat := (a.slots.find? (·.2 == v)).map (·.1)

def usesVar (v : Nat) (g : Gate) : Bool := g.a == v || (g.op != .not && g.b == v)

/-- Whether the variable is used by a later gate or is an output. -/
def live (rest : List Gate) (outs : List Nat) (v : Nat) : Bool :=
  outs.contains v || rest.any (usesVar v)

/-- How many gates until the variable's next use. -/
def nextUse (rest : List Gate) (outs : List Nat) (v : Nat) : Nat :=
  match rest.findIdx? (usesVar v) with
  | some i => i
  | none => if outs.contains v then rest.length else rest.length + 1

/-- Forget a dead variable, freeing its register and slot. -/
def kill (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    free := match a.regOf v with | some r => r :: a.free | none => a.free
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with | some k => k :: a.freeSlots | none => a.freeSlots }

/-- Evict the variable in register `r`, spilling it if it is in no slot. -/
def evict (a : Alloc) (r : XReg) (v : Nat) : Alloc :=
  let a := { a with regs := a.regs.filter (·.1 != r) }
  match a.slotOf v with
  | some _ => a
  | none => match a.freeSlots with
    | k :: ks =>
      { a with slots := (k, v) :: a.slots, freeSlots := ks,
               code := .movdquStore (spillAt k) r :: a.code }
    | [] => a

/-- A free register, evicting the value used farthest away, but not one of `keep`. -/
def getReg (a : Alloc) (rest : List Gate) (outs keep : List Nat) : Alloc × XReg :=
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

/-- The variable in a register, loading it from its slot if need be. -/
def inReg (a : Alloc) (rest : List Gate) (outs keep : List Nat) (v : Nat) : Alloc × XReg :=
  match a.regOf v with
  | some r => (a, r)
  | none =>
    let (a, r) := getReg a rest outs keep
    let a := match a.slotOf v with
      | some k => emit a [.movdquLoad r (spillAt k)]
      | none => a
    ({ a with regs := (r, v) :: a.regs }, r)

/-- Compile one gate, `rest` being the gates after it. -/
def gate (ones : XReg) (outs : List Nat) (a : Alloc) (g : Gate) (rest : List Gate) : Alloc :=
  let keep := [g.a, g.b]
  let (a, ra) := inReg a (g :: rest) outs keep g.a
  let (a, rb) := if g.op = .not then (a, ra) else inReg a (g :: rest) outs keep g.b
  let aDead := !live rest outs g.a
  let bDead := g.op != .not && g.b != g.a && !live rest outs g.b
  -- The instructions, in place of `ra` (`some true`), of `rb` (`some false`)
  -- or of a copy (`none`).
  let (tgt, is) : Option Bool × List Instr := match g.op with
    | .and | .or | .xor =>
      let op : XBinOp := match g.op with | .and => .pand | .or => .por | _ => .pxor
      if aDead then (some true, [xbin op ra rb])
      else if bDead then (some false, [xbin op rb ra])
      else (none, [xbin op ra rb])
    | .andn =>
      if bDead then (some false, [xbin .pandn rb ra])
      else if aDead then (some true, [xbin .por ra rb, xbin .pxor ra rb])
      else (none, [xbin .pandn rb ra])
    | .not => if aDead then (some true, [xbin .pxor ra ones]) else (none, [xbin .pxor ra ones])
  match tgt with
  | some inA =>
    let d := if inA then ra else rb
    let a := if aDead then kill a g.a else a
    let a := if bDead then kill a g.b else a
    let a := emit a is
    { a with regs := (d, g.dst) :: a.regs, free := a.free.filter (· != d) }
  | none =>
    -- a copy of the operand the instruction writes: `rb` for `pandn`, else `ra`
    let src := if g.op = .andn then rb else ra
    let (a, d) := getReg a rest outs keep
    let is := is.map fun i => match i with
      | .xop (.bin op r s) => if r = src then xbin op d s else i
      | _ => i
    let a := emit a (xbin .movdqa d src :: is)
    { a with regs := (d, g.dst) :: a.regs, free := a.free.filter (· != d) }

/-- Compile the gates. -/
def gates (ones : XReg) (outs : List Nat) : Alloc → List Gate → Alloc
  | a, [] => a
  | a, g :: gs => gates ones outs (gate ones outs a g gs) gs

/-- Move each output to its register. -/
def place (a : Alloc) : List (Nat × XReg) → Alloc
  | [] => a
  | (v, r) :: outs =>
    if a.regOf v = some r then place a outs else
    -- Evict whatever is in `r`.
    let a := match a.regs.find? (·.1 == r) with
      | some (_, u) => evict a r u
      | none => { a with free := a.free.filter (· != r) }
    let a := match a.regOf v with
      | some r' => emit a [xbin .movdqa r r']
      | none => match a.slotOf v with
        | some k => emit a [.movdquLoad r (spillAt k)]
        | none => a
    let a := { a with regs := (r, v) :: a.regs.filter (·.2 != v) }
    place a outs

end Alloc

/-- The code of a circuit whose inputs `ins` start in their registers, the
registers `free` being free, leaving the outputs `outs` in their registers,
spilling to the slots `spill` of the scratch buffer, with all ones in `ones`. -/
def compile (gs : List Gate) (ins outs : List (Nat × XReg)) (free : List XReg)
    (spill : List Nat) (ones : XReg) : List Instr :=
  let init : Alloc :=
    { regs := ins.map (fun (v, r) => (r, v)), slots := [], free := free, freeSlots := spill, code := [] }
  let a := Alloc.gates ones (outs.map (·.1)) init gs
  let a := Alloc.place a outs
  a.code.reverse

end VG.Impl.TripleDes.X86_64.BitsliceSse
