import VerifiedGarbage.Impl.TripleDes.BitsliceCircuit
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Register allocation of the DES S-box circuits on AdvSIMD registers

Compiles a circuit (`Bitslice.Gate`s, applied to 128-bit words) to
three-operand AdvSIMD instructions (`and`, `orr`, `eor`, `bic`, `not`),
every value in a vector register. A gate's result goes to the first free
register, after the registers of the operands that die there are freed, so
that it usually reuses one of them. The circuits need at most 15 values at
once, far fewer than the registers they are given, so nothing is spilled;
an allocation that ran out of registers would produce code that the proofs
reject.

Nothing here needs to be trusted: the proofs check the code this produces,
not the allocator.
-/

namespace VG.Impl.TripleDes.AArch64.BitsliceNeon

open VG.AArch64 VG.Impl.TripleDes.Bitslice

/-- The allocation state. -/
structure Alloc where
  /-- The variable each register holds. -/
  regs : List (VReg × Nat)
  free : List VReg
  /-- The instructions so far, most recent first. -/
  code : List Instr

namespace Alloc

def regOf (a : Alloc) (v : Nat) : VReg := ((a.regs.find? (·.2 == v)).map (·.1)).getD .v0

def usesVar (v : Nat) (g : Gate) : Bool := g.a == v || g.b == v

/-- Whether the variable is used by a later gate or is an output. -/
def live (rest : List Gate) (outs : List Nat) (v : Nat) : Bool :=
  outs.contains v || rest.any (usesVar v)

/-- Forget a dead variable, freeing its register. -/
def kill (a : Alloc) (v : Nat) : Alloc :=
  match a.regs.find? (·.2 == v) with
  | some (r, _) => { a with regs := a.regs.filter (·.2 != v), free := r :: a.free }
  | none => a

def opInstr (op : Op) (d p q : VReg) : Instr :=
  match op with
  | .and => .vop (.logic .and d p q)
  | .or => .vop (.logic .orr d p q)
  | .xor => .vop (.logic .eor d p q)
  | .andn => .vop (.logic .bic d p q)
  | .not => .vop (.not d p)

/-- Compile one gate, followed by the gates `rest`. -/
def gate (outs : List Nat) (a : Alloc) (g : Gate) (rest : List Gate) : Alloc :=
  let ra := a.regOf g.a
  let rb := a.regOf g.b
  let a := if live rest outs g.a then a else a.kill g.a
  let a := if live rest outs g.b then a else a.kill g.b
  match a.free with
  | rd :: rs => { regs := (rd, g.dst) :: a.regs, free := rs, code := opInstr g.op rd ra rb :: a.code }
  | [] => a

def gates (outs : List Nat) : Alloc → List Gate → Alloc
  | a, [] => a
  | a, g :: gs => gates outs (gate outs a g gs) gs

end Alloc

/-- The code of a circuit whose inputs `ins` (variable, register) start in
their registers, the registers `free` being free, and the registers its
outputs `outs` end in. -/
def compile (gs : List Gate) (ins : List (Nat × VReg)) (outs : List Nat) (free : List VReg) :
    List Instr × List VReg :=
  let a := Alloc.gates outs { regs := ins.map fun (v, r) => (r, v), free := free, code := [] } gs
  (a.code.reverse, outs.map a.regOf)

end VG.Impl.TripleDes.AArch64.BitsliceNeon
