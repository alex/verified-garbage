import VerifiedGarbage.Spec.Sha256
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# SHA-256 compression with the AArch64 SHA-2 instructions

`vg_sha256_compress_sha2(state = x0, blocks = x1, count = x2, scratch = x3)`.
The working state stays in `v0` and `v1`, four words per register. `v4`–`v7`
hold the sixteen-word schedule window. SHA256SU0/SHA256SU1 expand four
words at a time; SHA256H/SHA256H2 perform their four rounds. The original
state of each block is saved in `v16` and `v17` for feed-forward.

Constants are materialized through `w4` into `v3`. Only caller-saved
registers are used, and scratch is unused. The count and block pointer
control the only loop; message words never affect addresses or branches.
-/

namespace VG.Impl.Sha256.AArch64.Sha2

open VG.AArch64
open VG.Spec.Sha256 (K)

/-- The register holding schedule words `4i` through `4i+3`. -/
def msg (i : Nat) : VReg := [.v4, .v5, .v6, .v7].getD (i % 4) .v4

/-- Materialize one word of a round-constant vector. -/
def constant (i j : Nat) : List Instr :=
  [.movz .w .x4 ((K (4 * i + j)).extractLsb' 0 16) 0,
   .movk .w .x4 ((K (4 * i + j)).extractLsb' 16 16) 1,
   .vop (.ins .s4 .v3 j .x4)]

/-- Load the first sixteen words, then expand the schedule in registers. -/
def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.ldrq (msg i) .x1 (16 * i), .vop (.rev .rev32b (msg i) (msg i))]
  else
    [.vop (.sha256su0 (msg i) (msg (i + 1))),
     .vop (.sha256su1 (msg i) (msg (i + 2)) (msg (i + 3)))]

/-- Four rounds, retaining the old ABCD for SHA256H2. -/
def rounds4 (i : Nat) : List Instr :=
  (List.range 4).flatMap (constant i) ++
  [.vop (.add .s4 .v3 .v3 (msg i)),
   .vop (.mov .v2 .v0),
   .vop (.sha256h .v0 .v1 .v3),
   .vop (.sha256h2 .v1 .v2 .v3)]

def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds4 n))

def load : List Instr :=
  [.ldrq .v0 .x0 0, .ldrq .v1 .x0 16,
   .vop (.mov .v16 .v0), .vop (.mov .v17 .v1)]

def store : List Instr :=
  [.vop (.add .s4 .v0 .v0 .v16), .vop (.add .s4 .v1 .v1 .v17),
   .strq .v0 .x0 0, .strq .v1 .x0 16,
   .addImm .x .x1 .x1 64, .subImm .x .x2 .x2 1]

def body : Prog isa := .seq (.block load) (.seq (rounds 16) (.block store))

def compress : Prog isa :=
  .ite (.zero .x .x2) (.block []) (.loop body (.nonzero .x .x2))

end VG.Impl.Sha256.AArch64.Sha2
