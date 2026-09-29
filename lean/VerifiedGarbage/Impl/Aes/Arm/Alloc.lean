import VerifiedGarbage.Impl.Aes.Circuit
import VerifiedGarbage.TCB.Arm.Isa

/-!
# Register allocation of Boolean circuits on ARMv7

Compiles a circuit (`Circuit.Gate`s on 32-bit words) to three-operand ARM
instructions (`eor`, `and`), with the words in registers and, when the
registers run out, in 4-byte slots `[sb, #4k]` of a scratch buffer (whose
base is in the register `sb`). Both operands of a gate must be in
registers: an operand that is only in a slot is loaded first. A gate's
result goes to the register of an operand that dies there if there is one,
and otherwise to a free register. When no register is free, the value
whose next use is farthest away (Belady) is evicted, and spilled to a slot
unless it is already in one.

The model has no `mvn` (nor `bic`/`orn`), and there are too few registers
to keep all ones in one, so `a ⊕ ¬b` is compiled as the two gates
`t := a ⊕ b` and `t ⊕ ones`, where `ones` is one more variable of the
circuit, which starts in a slot (written by the code first) and is loaded
like any spilled value.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

namespace VG.Impl.Aes.Arm

open VG.Arm VG.Impl.Aes.Circuit

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

def emit (a : Alloc) (i : Instr) : Alloc := { a with code := i :: a.code }

/-- Evict the variable in register `r`, spilling it if it is in no slot. -/
def evict (a : Alloc) (r : Reg) (v : Nat) : Alloc :=
  let a := { a with regs := a.regs.filter (·.1 != r) }
  match a.slotOf v with
  | some _ => a
  | none => match a.freeSlots with
    | k :: ks =>
      emit { a with slots := (k, v) :: a.slots, freeSlots := ks } (.str r sb (4 * k))
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
    | none => (a, .r0)

/-- Make sure the variable is in a register, loading it from its slot. -/
def load (a : Alloc) (rest : List Gate) (keep : List Nat) (v : Nat) : Alloc × Reg :=
  match a.regOf v with
  | some r => (a, r)
  | none =>
    let (a, r) := getReg sb a rest keep
    let a := emit a (.ldr r sb (4 * (a.slotOf v).getD 0))
    ({ a with regs := (r, v) :: a.regs }, r)

def opInstr (op : Op) (d p q : Reg) : Instr :=
  match op with
  | .and => .dp .and d p (.reg q)
  | _ => .dp .eor d p (.reg q)

/-- Compile one gate, `rest` being the gates after it. -/
def gate (outs : List (Nat × Reg)) (a : Alloc) (g : Gate) (rest : List Gate) : Alloc :=
  let (a, ra) := load sb a (g :: rest) [g.a, g.b] g.a
  let (a, rb) := load sb a (g :: rest) [g.a, g.b] g.b
  let aDead := !live rest outs g.a
  let bDead := !live rest outs g.b
  -- The result goes to its output register if that is free, and otherwise to
  -- the register of an operand that dies here.
  let a := if aDead then kill a g.a else a
  let a := if bDead then kill a g.b else a
  let target := (outs.find? (·.1 == g.dst)).map (·.2)
  let (a, rd) :=
    match target with
    | some r => if a.free.contains r then ({ a with free := a.free.filter (· != r) }, r)
      else if aDead then ({ a with free := a.free.filter (· != ra) }, ra)
      else if bDead then ({ a with free := a.free.filter (· != rb) }, rb)
      else getReg sb a rest [g.a, g.b]
    | none =>
    if aDead then ({ a with free := a.free.filter (· != ra) }, ra)
    else if bDead then ({ a with free := a.free.filter (· != rb) }, rb)
    else getReg sb a rest [g.a, g.b]
  let a := emit a (opInstr g.op rd ra rb)
  { a with regs := (rd, g.dst) :: a.regs }

/-- Compile the gates. -/
def gates (outs : List (Nat × Reg)) : Alloc → List Gate → Alloc
  | a, [] => a
  | a, g :: gs => gates outs (gate sb outs a g gs) gs

/-- Move each output to its register. -/
def place (a : Alloc) : List (Nat × Reg) → Alloc
  | [] => a
  | (v, r) :: outs =>
    if a.regOf v = some r then place a outs else
    -- Evict whatever is in `r`.
    let a := match a.regs.find? (·.1 == r) with
      | some (_, u) => evict sb a r u
      | none => { a with free := a.free.filter (· != r) }
    let a := match a.regOf v with
      | some r' => emit a (.mov r (.reg r'))
      | none => emit a (.ldr r sb (4 * (a.slotOf v).getD 0))
    let a := { a with regs := (r, v) :: a.regs.filter (·.2 != v) }
    place a outs

end Alloc

/-- `d := a ⊕ ¬b` as `t := a ⊕ b; d := t ⊕ ones`, with the variables
`t` numbered from `fresh` on. -/
def splitXnor (ones : Nat) : Nat → List Gate → List Gate
  | _, [] => []
  | fresh, g :: gs =>
    if g.op = .xnor then xor fresh g.a g.b :: xor g.dst fresh ones :: splitXnor ones (fresh + 1) gs
    else g :: splitXnor ones fresh gs

/-- The code of a circuit whose inputs `ins` start in their registers, the
registers `free` being free, leaving the outputs `outs` in their registers.
`ones` is the slot to hold all ones (written by the code first, from the
first free register) and `onesVar` the circuit's variable for it; `fresh`
numbers the variables of `splitXnor`; `spill` are the slots it may spill
to. -/
def compile (sb : Reg) (gs : List Gate) (ins outs : List (Nat × Reg)) (free : List Reg)
    (ones onesVar fresh : Nat) (spill : List Nat) : List Instr :=
  let r := free.headD .r0
  let init : Alloc :=
    { regs := ins.map (fun (v, r) => (r, v)), slots := [(ones, onesVar)], free := free,
      freeSlots := spill, code := [] }
  let a := Alloc.gates sb outs init (splitXnor onesVar fresh gs)
  let a := Alloc.place sb a outs
  [.mov r (.imm 0), .dp .sub r r (.imm 1), .str r sb (4 * ones)] ++ a.code.reverse

end VG.Impl.Aes.Arm
