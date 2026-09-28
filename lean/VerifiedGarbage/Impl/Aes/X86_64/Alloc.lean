import VerifiedGarbage.Impl.Aes.Circuit
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# Register allocation of Boolean circuits on x86-64

Compiles a circuit (`Circuit.Gate`s on 64-bit words) to two-operand x86-64
instructions, with the words in registers and, when the registers run out,
in 8-byte slots `[sb + 8k]` of a scratch buffer (whose base is in the
register `sb`). A gate is computed in place when one of its operands dies
there; otherwise its first operand is copied to a free register first. When
no register is free, the value whose next use is farthest away (Belady) is
evicted, and spilled to a slot unless it is already in one; an operand in a
slot is used as a memory operand. `¬b` is `b ⊕ [ones]`, a slot holding all
ones.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

namespace VG.Impl.Aes.X86_64

open VG.X86_64 VG.Impl.Aes.Circuit

/-- Slot `k` of the scratch buffer whose base is in `sb`. -/
def slotAt (sb : Reg) (k : Nat) : MemOp := { base := sb, disp := ((8 * k : Nat) : Int) }

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

variable (sb : Reg)

def regOf (a : Alloc) (v : Nat) : Option Reg := (a.regs.find? (·.2 == v)).map (·.1)

def slotOf (a : Alloc) (v : Nat) : Option Nat := (a.slots.find? (·.2 == v)).map (·.1)

/-- Where the variable is, as an operand (a register if it is in one). -/
def src (a : Alloc) (v : Nat) : Src :=
  match a.regOf v with
  | some r => .reg r
  | none => match a.slotOf v with
    | some k => .mem (slotAt sb k)
    | none => .imm 0

def usesVar (v : Nat) (g : Gate) : Bool := g.a == v || g.b == v

/-- Whether the variable is used by a later gate or is an output. -/
def live (rest : List Gate) (outs : List (Nat × Reg)) (v : Nat) : Bool :=
  outs.any (·.1 == v) || rest.any (usesVar v)

/-- How many gates until the variable's next use. -/
def nextUse (rest : List Gate) (v : Nat) : Nat := (rest.findIdx? (usesVar v)).getD rest.length

/-- Forget a dead variable, freeing its register and slot. -/
def kill (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    free := match a.regOf v with | some r => r :: a.free | none => a.free
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with | some k => k :: a.freeSlots | none => a.freeSlots }

/-- Evict the variable in register `r`, spilling it if it is in no slot. -/
def evict (a : Alloc) (r : Reg) (v : Nat) : Alloc :=
  let a := { a with regs := a.regs.filter (·.1 != r) }
  match a.slotOf v with
  | some _ => a
  | none => match a.freeSlots with
    | k :: ks =>
      { a with slots := (k, v) :: a.slots, freeSlots := ks, code := .store (slotAt sb k) r :: a.code }
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
    | some (r, v) => (evict sb a r v, r)
    | none => (a, .rax)

def emit (a : Alloc) (i : Instr) : Alloc := { a with code := i :: a.code }

def opInstrs (ones : Nat) (op : Op) (d : Reg) (s : Src) : List Instr :=
  match op with
  | .xor => [.alu .xor d s]
  | .and => [.alu .and d s]
  | .xnor => [.alu .xor d s, .alu .xor d (.mem (slotAt sb ones))]

/-- Compile one gate, `rest` being the gates after it. -/
def gate (ones : Nat) (outs : List (Nat × Reg)) (a : Alloc) (g : Gate) (rest : List Gate) : Alloc :=
  let aDead := !live rest outs g.a
  let bDead := !live rest outs g.b
  -- Compute in place into an operand that dies here (every operation is symmetric).
  let (p, q, pDead, qDead) :=
    if aDead && (a.regOf g.a).isSome then (g.a, g.b, aDead, bDead)
    else if bDead && (a.regOf g.b).isSome then (g.b, g.a, bDead, aDead)
    else (g.a, g.b, aDead, bDead)
  let a := match a.regOf p, pDead with
    | some rp, true =>
      let a := (opInstrs sb ones g.op rp (src sb a q)).foldl emit a
      let a := if qDead then kill a q else a
      let a := kill a p
      { a with free := a.free.filter (· != rp), regs := (rp, g.dst) :: a.regs }
    | _, _ =>
      let (a, rd) := getReg sb a rest [p, q]
      let a := emit a (.mov rd (src sb a p))
      let a := (opInstrs sb ones g.op rd (src sb a q)).foldl emit a
      let a := if pDead then kill a p else a
      let a := if qDead then kill a q else a
      { a with regs := (rd, g.dst) :: a.regs }
  a

/-- Compile the gates. -/
def gates (ones : Nat) (outs : List (Nat × Reg)) : Alloc → List Gate → Alloc
  | a, [] => a
  | a, g :: gs => gates ones outs (gate sb ones outs a g gs) gs

/-- Move each output to its register. -/
def place (a : Alloc) : List (Nat × Reg) → Alloc
  | [] => a
  | (v, r) :: outs =>
    if a.regOf v = some r then place a outs else
    -- Evict whatever is in `r`.
    let a := match a.regs.find? (·.1 == r) with
      | some (_, u) => evict sb a r u
      | none => { a with free := a.free.filter (· != r) }
    let a := emit a (.mov r (src sb a v))
    let a := { a with regs := (r, v) :: a.regs.filter (·.2 != v) }
    place a outs

end Alloc

/-- The code of a circuit whose inputs `ins` start in their registers, the
registers `free` being free, leaving the outputs `outs` in their registers.
`ones` is the slot to hold all ones (written by the code first, from the
first free register), and `spill` the slots it may spill to. -/
def compile (sb : Reg) (gs : List Gate) (ins outs : List (Nat × Reg)) (free : List Reg)
    (ones : Nat) (spill : List Nat) : List Instr :=
  let r := free.headD .rax
  let init : Alloc :=
    { regs := ins.map (fun (v, r) => (r, v)), slots := [], free := free, freeSlots := spill, code := [] }
  let a := Alloc.gates sb ones outs init gs
  let a := Alloc.place sb a outs
  [.movImm64 r (BitVec.allOnes 64), .store (slotAt sb ones) r] ++ a.code.reverse

end VG.Impl.Aes.X86_64
