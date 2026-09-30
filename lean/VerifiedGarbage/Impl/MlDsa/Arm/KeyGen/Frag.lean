import VerifiedGarbage.Impl.MlKem.Arm.Top
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on 32-bit ARM: the pieces of the top-level functions

`vg_mldsa*_keygen` and `vg_mldsa*_verify` are sequences of calls of ML-DSA's
polynomial primitives (`Spec/MlDsa/Poly.lean`) and of the SHA-3 sponge
functions, on buffers in their working space `scratch` and their arguments.
Like ML-KEM's top-level functions (`Impl/MlKem/Arm/Top.lean`, whose sponge
routine `hash` and byte copy `copy` they use), they keep `scratch` in `r7`
and their other arguments in `r4`, `r5` and `r6`, the AND of the results so
far in `r11`, and save our caller's `r4`–`r11` and `lr` in `scratch` (at
840, `oSave`): all callee-saved registers, which the functions they call
preserve.

A buffer is at `p.1 + p.2` for a pointer `p` (a register and an offset).
Each call is preceded by the moves of its arguments into `r0`–`r3` (`glue`):
`movw` and `movt` of the offset (or of an integer argument), then an `add` of
the register for a pointer, so that any offset or integer can be moved,
whatever the parameter set. A fifth argument goes on the stack: it is moved
into `r12`, which a call changes anyway, and pushed in a frame of its own
around the call (`callAtS`), whose pop loads it back into `r12`.
-/

namespace VG.Impl.MlDsa.Arm.KeyGen

open VG.Arm

/-- A pointer: a register and an offset. -/
abbrev Ptr := Reg × Nat

/-! ## Moves -/

/-- `d ← v` (modulo 2³²): `movw` of the low half and `movt` of the high half. -/
def ldc (d : Reg) (v : Nat) : List Instr :=
  [.movw d (BitVec.ofNat 16 v), .movt d (BitVec.ofNat 16 (v / 65536))]

/-- An argument: a pointer, or an integer. -/
inductive Arg
  | ptr (p : Ptr)
  | imm (v : Nat)

/-- `d ← a`. -/
def Arg.instrs (d : Reg) : Arg → List Instr
  | .ptr p => ldc d p.2 ++ [.dp .add d p.1 (.reg d)]
  | .imm v => ldc d v

/-- The moves of the arguments `as` into their registers. -/
def glue : List (Reg × Arg) → List Instr
  | [] => []
  | (d, a) :: as => a.instrs d ++ glue as

/-- The moves of the arguments, then a call. -/
def callAt (name : String) (c : Prog isa) (as : List (Reg × Arg)) : Prog isa :=
  .seq (.block (glue as)) (.call name c)

/-- The moves of the arguments and of the stack argument `st` into `r12`,
then a call in a frame that pushes `r12`. -/
def callAtS (name : String) (c : Prog isa) (as : List (Reg × Arg)) (st : Arg) : Prog isa :=
  .seq (.block (glue as ++ st.instrs .r12)) (.frame (.push [.r12]) (.call name c) (.pop .r12 4))

/-- The byte `v` to `p` (`p.2 < 4096`). -/
def setB (p : Ptr) (v : Nat) : List Instr := [.movw .r12 (BitVec.ofNat 16 v), .strb .r12 p.1 p.2]

/-- `f a, f (a + 1), …, f (a + n - 1)`, in sequence. -/
def seqR (f : Nat → Prog isa) (a : Nat) : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (f a) (seqR f (a + 1) n)

/-! ## Results -/

/-- `r11 ← r11 ∧ r0`. -/
def and11 : List Instr := [.dp .and .r11 .r11 (.reg .r0)]

def maskBody : List Instr :=
  [.ldr .r3 .r1 0, .dp .and .r3 .r3 (.reg .r12), .str .r3 .r1 0, .dp .add .r1 .r1 (.imm 4), .subs .r2 .r2 (.imm 1)]

/-- The polynomial at `a` masked by the result `r0` (0 or 1) of the sampler
that wrote it: unchanged if 1, and zero if 0, so that it is reduced either
way, without a branch. `r12 ← -r0`, then each coefficient `∧ r12`. -/
def mask (a : Ptr) : Prog isa :=
  .seq (.block ([.mov .r12 (.imm 0), .dp .sub .r12 .r12 (.reg .r0)] ++ Arg.instrs .r1 (.ptr a) ++
      [.mov .r2 (.imm 256)]))
    (.loop (.block maskBody) .ne)

/-- A sampler's call, its result ANDed into `r11`, and its output masked. -/
def sampled (call : Prog isa) (a : Ptr) : Prog isa :=
  .seq call (.seq (.block and11) (mask a))

/-! ## Entry and exit -/

/-- Our caller's `r4`–`r11` and `lr` saved in `scratch` (in `r3`), the
arguments moved to `r4`–`r7`, and `r11 ← 1`. -/
def pro : List Instr :=
  Impl.MlKem.Arm.saveRegs .r3 Impl.MlKem.Arm.oSave ++
    ([.str .lr .r3 (Impl.MlKem.Arm.oSave + 32), .mov .r4 (.reg .r0), .mov .r5 (.reg .r1),
      .mov .r6 (.reg .r2), .mov .r7 (.reg .r3), .mov .r11 (.imm 1)] : List Instr)

end VG.Impl.MlDsa.Arm.KeyGen
