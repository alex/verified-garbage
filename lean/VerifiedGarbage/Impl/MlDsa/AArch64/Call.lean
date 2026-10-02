import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen

/-!
# ML-DSA on AArch64: calls with their arguments

The top-level functions (`vg_mldsa*_keygen`, `vg_mldsa*_sign`,
`vg_mldsa*_verify`) are sequences of calls on buffers whose addresses they
keep in callee-saved registers. A buffer is at `p.1 + p.2` for a pointer `p`
(a register and an offset). Each call is preceded by the moves of its
arguments into their registers (`glue`: an `add`, or a `movz` (and `movk`s)
and an `add`, for a pointer; a `movz` (and `movk`s) for an integer).
-/

namespace VG.Impl.MlDsa.AArch64

open VG.AArch64

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-- `scratch + off`: the functions keep the address of their working space in `x28`. -/
abbrev sc (off : Nat) : Ptr := (.x28, off)

/-- `d ← v`: a `movz`, or for `v ≥ 2¹⁶` a `movz` and three `movk`s. -/
def movV (d : Reg) (v : Nat) : List Instr :=
  if v < 65536 then [.movz .x d (BitVec.ofNat 16 v) 0] else Impl.MlKem.AArch64.movImm d (BitVec.ofNat 64 v)

/-- `d ← b + off` (for `d ≠ b`). -/
def lea (d b : Reg) (off : Nat) : List Instr :=
  if off < 4096 then [.addImm .x d b off] else movV d off ++ [.add .x d b d]

/-- An argument: a pointer, or an integer (an immediate). -/
inductive Arg
  | ptr (p : Ptr)
  | imm (v : Nat)

/-- `d ← a`. -/
def Arg.instrs (d : Reg) : Arg → List Instr
  | .ptr p => lea d p.1 p.2
  | .imm v => movV d v

/-- The moves of the arguments `as` into their registers. -/
def glue : List (Reg × Arg) → List Instr
  | [] => []
  | (d, a) :: as => a.instrs d ++ glue as

/-- The moves of the arguments, then a call. -/
def callAt (name : String) (c : Prog isa) (as : List (Reg × Arg)) : Prog isa :=
  .seq (.block (glue as)) (.call name c)

/-- The byte `v` to `p` (`p.2 < 4096`), through `x9`. -/
def setB (p : Ptr) (v : Nat) : List Instr := [.movz .x .x9 (BitVec.ofNat 16 v) 0, .strb .x9 p.1 p.2]

/-- `x24 ← x24 ∧ w0`, in 32 bits (a callee's `u32` result is `w0`, and the
upper half of `x0` is unspecified): the AND of the results that decide
whether the function goes on. -/
def and24 : List Instr := [.logic .and .w .x24 .x24 .x0]

end VG.Impl.MlDsa.AArch64
