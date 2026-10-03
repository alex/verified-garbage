import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Register allocation of the DES S-box circuits on x86-64

Compiles a circuit (`Bitslice.Gate`s on 64-bit words) to two-operand
x86-64 instructions, with the words in registers and, when the registers
run out, in 8-byte slots `[rcx + 8k]` of the scratch buffer. A gate is computed
in place when one of its operands dies there; otherwise its first operand
is copied to a free register first. `a ∧ ¬b` is `¬b ∧ a` in place of a dead
`b`, `(a ∨ b) ⊕ b` in place of a dead `a`; `¬a` is `a ⊕ [all ones]` (the
immediate `-1`). When no register is free, the value whose next use is
farthest away (Belady) is evicted, and spilled to a slot unless it is
already in one; an operand in a slot is used as a memory operand.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

namespace VG.Impl.TripleDes.X86_64.Bitslice

open VG.X86_64 VG.Impl.TripleDes.Bitslice

/-- Spill slot `k`, in the scratch buffer. -/
def spillAt (k : Nat) : MemOp := { base := .rcx, disp := ((8 * k : Nat) : Int) }

/-- The allocation state. -/
structure Alloc where
  /-- The variable each register holds. -/
  regs : List (Reg × Nat)
  /-- The variable each slot holds. -/
  slots : List (Nat × Nat)
  free : List Reg
  freeSlots : List Nat
  /-- The instructions so far, most recent first. -/
  code : List Instr

namespace Alloc

def regOf (a : Alloc) (v : Nat) : Option Reg := (a.regs.find? (·.2 == v)).map (·.1)

def slotOf (a : Alloc) (v : Nat) : Option Nat := (a.slots.find? (·.2 == v)).map (·.1)

/-- Where the variable is, as an operand (a register if it is in one). -/
def src (a : Alloc) (v : Nat) : Src :=
  match a.regOf v with
  | some r => .reg r
  | none => match a.slotOf v with
    | some k => .mem (spillAt k)
    | none => .imm 0

def usesVar (v : Nat) (g : Gate) : Bool := g.a == v || g.b == v

/-- Whether the variable is used by a later gate or is an output. -/
def live (rest : List Gate) (outs : List Nat) (v : Nat) : Bool :=
  outs.contains v || rest.any (usesVar v)

/-- How many gates until the variable's next use. -/
def nextUse (rest : List Gate) (v : Nat) : Nat := (rest.findIdx? (usesVar v)).getD rest.length

/-- Forget a dead variable, freeing its register and slot. -/
def kill (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    free := match a.regOf v with | some r => r :: a.free | none => a.free
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with | some k => k :: a.freeSlots | none => a.freeSlots }

/-- Forget a variable's register (it is about to be overwritten), keeping
the register out of the free list, and free its slot. -/
def reuse (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with | some k => k :: a.freeSlots | none => a.freeSlots }

/-- Evict the variable in register `r`, spilling it if it is in no slot. -/
def evict (a : Alloc) (r : Reg) (v : Nat) : Alloc :=
  let a := { a with regs := a.regs.filter (·.1 != r) }
  match a.slotOf v with
  | some _ => a
  | none => match a.freeSlots with
    | k :: ks =>
      { a with slots := (k, v) :: a.slots, freeSlots := ks, code := .store (spillAt k) r :: a.code }
    | [] => a

/-- A free register, evicting the value used farthest away, but not one of `keep`. -/
def getReg (a : Alloc) (rest : List Gate) (keep : List Nat) : Alloc × Reg :=
  match a.free with
  | r :: rs => ({ a with free := rs }, r)
  | [] =>
    let cands := a.regs.filter fun p => !keep.contains p.2
    let best := cands.foldl (fun (b : Option (Reg × Nat)) p =>
      match b with
      | none => some p
      | some q => if nextUse rest p.2 > nextUse rest q.2 then some p else some q) none
    match best with
    | some (r, v) => (evict a r v, r)
    | none => (a, .rax)

def emit (a : Alloc) (is : List Instr) : Alloc := { a with code := is.reverse ++ a.code }

def ones : Src := .imm (BitVec.allOnes 32)

/-- Compile one gate, `rest` being the gates after it. -/
def gate (outs : List Nat) (a : Alloc) (g : Gate) (rest : List Gate) : Alloc :=
  let aDead := !live rest outs g.a
  let bDead := !live rest outs g.b
  let fin (a : Alloc) (r : Reg) : Alloc :=
    let a := if aDead then kill a g.a else a
    let a := if bDead then kill a g.b else a
    { a with regs := (r, g.dst) :: a.regs, free := a.free.filter (· != r) }
  match g.op with
  | .not =>
    match a.regOf g.a, aDead with
    | some r, true => fin (emit (reuse a g.a) [.alu .xor r ones]) r
    | _, _ =>
      let (a, r) := getReg a rest [g.a]
      fin (emit a [.mov r (src a g.a), .alu .xor r ones]) r
  | .andn =>
    match a.regOf g.b, bDead, a.regOf g.a, aDead with
    | some r, true, _, _ => fin (emit (reuse a g.b) [.alu .xor r ones, .alu .and r (src a g.a)]) r
    | _, _, some r, true =>
      fin (emit (reuse a g.a) [.alu .or r (src a g.b), .alu .xor r (src a g.b)]) r
    | _, _, _, _ =>
      let (a, r) := getReg a rest [g.a, g.b]
      fin (emit a [.mov r (src a g.b), .alu .xor r ones, .alu .and r (src a g.a)]) r
  | op =>
    let aluOp : AluOp := match op with | .and => .and | .or => .or | _ => .xor
    match a.regOf g.a, aDead, a.regOf g.b, bDead with
    | some r, true, _, _ => fin (emit (reuse a g.a) [.alu aluOp r (src a g.b)]) r
    | _, _, some r, true => fin (emit (reuse a g.b) [.alu aluOp r (src a g.a)]) r
    | _, _, _, _ =>
      let (a, r) := getReg a rest [g.a, g.b]
      fin (emit a [.mov r (src a g.a), .alu aluOp r (src a g.b)]) r

/-- Compile the gates. -/
def gates (outs : List Nat) : Alloc → List Gate → Alloc
  | a, [] => a
  | a, g :: gs => gates outs (gate outs a g gs) gs

/-- Move each output to its register. -/
def place (a : Alloc) : List (Nat × Reg) → Alloc
  | [] => a
  | (v, r) :: outs =>
    if a.regOf v = some r then place a outs else
    -- Evict whatever is in `r`.
    let a := match a.regs.find? (·.1 == r) with
      | some (_, u) => evict a r u
      | none => { a with free := a.free.filter (· != r) }
    let a := emit a [.mov r (src a v)]
    let a := { a with regs := (r, v) :: a.regs.filter (·.2 != v) }
    place a outs

end Alloc

/-- The code of a circuit whose inputs `ins` start in their registers, the
registers `free` being free, leaving the outputs `outs` in their registers,
and spilling to the slots `spill` of the scratch buffer. -/
def compile (gs : List Gate) (ins outs : List (Nat × Reg)) (free : List Reg)
    (spill : List Nat) : List Instr :=
  let init : Alloc :=
    { regs := ins.map (fun (v, r) => (r, v)), slots := [], free := free, freeSlots := spill, code := [] }
  let a := Alloc.gates (outs.map (·.1)) init gs
  let a := Alloc.place a outs
  a.code.reverse

end VG.Impl.TripleDes.X86_64.Bitslice
