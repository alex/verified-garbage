import VerifiedGarbage.Impl.Aes.Circuit
import VerifiedGarbage.TCB.X86.Isa

/-!
# Register allocation of Boolean circuits on x86 (32-bit)

Compiles a circuit (`Circuit.Gate`s on 32-bit words) to two-operand x86
instructions, as `Impl/Aes/X86_64/Alloc.lean` does, but for a machine with
few registers: the inputs start in 4-byte slots `[sb + 4k]` of a scratch
buffer (whose base is in the register `sb`), and the outputs end in slots.
A gate is computed in place when one of its operands dies there; otherwise
its first operand is copied to a free register first. When no register is
free, the value whose next use is farthest away (Belady) is evicted, and
spilled to a slot unless it is already in one; an operand in a slot is used
as a memory operand. Only the spill slots are reused: an input's slot keeps
it until the end, when the outputs are stored. `¬b` is `b ⊕ 0xFFFFFFFF`.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

namespace VG.Impl.Aes.X86

open VG.X86 VG.Impl.Aes.Circuit

/-- Slot `k` of the scratch buffer whose base is in `sb`. -/
def slotAt (sb : Reg) (k : Nat) : MemOp := { base := sb, disp := 4 * k }

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

variable (sb : Reg) (spill : List Nat)

def regOf (a : Alloc) (v : Nat) : Option Reg := (a.regs.find? (·.2 == v)).map (·.1)

def slotOf (a : Alloc) (v : Nat) : Option Nat := (a.slots.find? (·.2 == v)).map (·.1)

/-- Where the variable is, as an operand (a register if it is in one). -/
def src (a : Alloc) (v : Nat) : Src :=
  match a.regOf v with
  | some r => .reg r
  | none => match a.slotOf v with
    | some k => .mem (slotAt sb k)
    | none => .imm 0

/-- Whether the variable is used by a later gate or is an output. -/
def live (rest : Rest) (outs : List (Nat × Nat)) (v : Nat) : Bool :=
  outs.any (·.1 == v) || rest.reads v

/-- How many gates until the variable's next use (as `2 ^` that, `Rest.nextUse`). -/
def nextUse (rest : Rest) (v : Nat) : Nat := rest.nextUse v

/-- Forget a dead variable, freeing its register and, if it is a spill slot, its slot. -/
def kill (a : Alloc) (v : Nat) : Alloc :=
  { a with
    regs := a.regs.filter (·.2 != v)
    free := match a.regOf v with | some r => r :: a.free | none => a.free
    slots := a.slots.filter (·.2 != v)
    freeSlots := match a.slotOf v with
      | some k => if spill.contains k then k :: a.freeSlots else a.freeSlots
      | none => a.freeSlots }

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
def getReg (a : Alloc) (rest : Rest) (keep : List Nat) : Alloc × Reg :=
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
    | none => (a, .eax)

def emit (a : Alloc) (i : Instr) : Alloc := { a with code := i :: a.code }

def opInstrs (op : Op) (d : Reg) (s : Src) : List Instr :=
  match op with
  | .xor => [.alu .xor d s]
  | .and => [.alu .and d s]
  | .xnor => [.alu .xor d s, .alu .xor d (.imm (BitVec.allOnes 32))]

/-- Compile one gate, `rest` being the gates after it. -/
def gate (outs : List (Nat × Nat)) (a : Alloc) (g : Gate) (rest : Rest) : Alloc :=
  let aDead := !live rest outs g.a
  let bDead := !live rest outs g.b
  -- Compute in place into an operand that dies here (every operation is symmetric).
  let (p, q, pDead, qDead) :=
    if aDead && (a.regOf g.a).isSome then (g.a, g.b, aDead, bDead)
    else if bDead && (a.regOf g.b).isSome then (g.b, g.a, bDead, aDead)
    else (g.a, g.b, aDead, bDead)
  let a := match a.regOf p, pDead with
    | some rp, true =>
      let a := (opInstrs g.op rp (src sb a q)).foldl emit a
      let a := if qDead then kill spill a q else a
      let a := kill spill a p
      { a with free := a.free.filter (· != rp), regs := (rp, g.dst) :: a.regs }
    | _, _ =>
      let (a, rd) := getReg sb a rest [p, q]
      let a := emit a (.mov rd (src sb a p))
      let a := (opInstrs g.op rd (src sb a q)).foldl emit a
      let a := if pDead then kill spill a p else a
      let a := if qDead then kill spill a q else a
      { a with regs := (rd, g.dst) :: a.regs }
  a

/-- Compile the gates. -/
def gates (outs : List (Nat × Nat)) : Rest → Alloc → List Gate → Alloc
  | _, a, [] => a
  | r, a, g :: gs => gates outs r.tail (gate sb spill outs a g r.tail) gs

/-- Store each output in a register to its slot. -/
def placeRegs (a : Alloc) : List (Nat × Nat) → Alloc
  | [] => a
  | (v, k) :: outs => match a.regOf v with
    | some r => placeRegs (emit a (.store (slotAt sb k) r)) outs
    | none => placeRegs a outs

/-- Move each output in no register from its slot to its own, through `t`. -/
def placeSlots (t : Reg) (a : Alloc) : List (Nat × Nat) → Alloc
  | [] => a
  | (v, k) :: outs => match a.regOf v, a.slotOf v with
    | none, some j => placeSlots t (emit (emit a (.mov t (.mem (slotAt sb j)))) (.store (slotAt sb k) t)) outs
    | _, _ => placeSlots t a outs

end Alloc

/-- The code of a circuit whose inputs `ins` (variable, slot) start in their
slots, the registers `free` being free, leaving the outputs `outs` in their
slots. `spill` are the slots it may spill to, apart from those of `ins`. -/
def compile (sb : Reg) (gs : List Gate) (ins outs : List (Nat × Nat)) (free : List Reg)
    (spill : List Nat) : List Instr :=
  let init : Alloc :=
    { regs := [], slots := ins.map (fun (v, k) => (k, v)), free := free, freeSlots := spill, code := [] }
  let a := Alloc.gates sb spill outs (Rest.ofGates gs) init gs
  let a := Alloc.placeRegs sb a outs
  let a := Alloc.placeSlots sb (free.headD .eax) a outs
  a.code.reverse

end VG.Impl.Aes.X86
