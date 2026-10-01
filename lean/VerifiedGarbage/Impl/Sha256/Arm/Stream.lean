import VerifiedGarbage.Impl.Sha256.Arm
import VerifiedGarbage.Impl.MdStream.Arm

/-!
# Streaming SHA-256: 32-bit ARM implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`).

* `init(state = r0)` stores the initial hash value (`init224`, SHA-224's).
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_sha256_compress`) with `scratch[0..112)` as its scratch space, and saving our
  caller's `r4`–`r11` and `lr` in `scratch[112..148)`.

HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 call the compression function the same
way (`saved`, `save`, `restore`, `compressAt`).
-/

namespace VG.Impl.Sha256.Arm.Stream

open VG.Arm
open VG.Impl.Sha256.Arm (compress)

/-- Stores the initial hash value `iv`. -/
def initWith (iv : Spec.Sha256.HashValue) : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movw .r12 (iv[k]!.extractLsb' 0 16),
     .movt .r12 (iv[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-- `vg_sha256_init`. -/
def init : Prog isa := initWith Spec.Sha256.H0

/-- `vg_sha224_init`. -/
def init224 : Prog isa := initWith Spec.Sha256.H0_224

/-- The callee-saved registers we use (and `lr`), and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r4, 112), (.r5, 116), (.r6, 120), (.r7, 124), (.r8, 128), (.r9, 132), (.r10, 136), (.r11, 140),
    (.lr, 144)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str r b d

/-- Restore them from `scratch` in `r3`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r3 d

/-- A call of `vg_sha256_compress`. -/
def compressCall : Prog isa := .call "vg_sha256_compress" compress

/-- Compress the block at `r1` into the hash value at `r0`, with scratch
space `r3`. -/
def compressAt : Prog isa := .seq (.block [.mov .r2 (.imm 1)]) compressCall

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/Arm.lean`). -/

def params : MdStream.Arm.Params where
  N := 32
  so := 112
  len := MdStream.Arm.len64 88 true
  out := MdStream.Arm.out32 8 true

def update : Prog isa := MdStream.Arm.update params "vg_sha256_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_sha256_compress" compress

end VG.Impl.Sha256.Arm.Stream
