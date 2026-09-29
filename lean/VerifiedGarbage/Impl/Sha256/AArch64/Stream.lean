import VerifiedGarbage.Impl.Sha256.AArch64
import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# Streaming SHA-256: AArch64 implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`).

* `init(state = x0)` stores `H⁽⁰⁾`.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_sha256_compress`) with `scratch[0..112)` as its scratch space, and
  saving our caller's `x19`–`x24` in `scratch[112..160)`.

HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 call the compression function the same
way (`saved`, `save`, `restore`, `compressAt`).
-/

namespace VG.Impl.Sha256.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha256.AArch64 (compress)

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

def init : Prog isa :=
  .block ((List.range 8).flatMap fun k =>
    [.movz .w .x9 (Spec.Sha256.H0[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Sha256.H0[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.x19, 112), (.x20, 120), (.x21, 128), (.x22, 136), (.x23, 144), (.x24, 152)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .str .x r b d

/-- Restore them from `scratch` in `x20` (`x20`, the base, last). -/
def restore : List Instr :=
  (saved.filter (·.1 != .x20)).map (fun (r, d) => .ldr .x r .x20 d) ++ [.ldr .x .x20 .x20 120]

/-- Compress the block at `x1` into the hash value at `x19`, with scratch
space `x20`. -/
def compressAt : Prog isa :=
  .seq (.block [mov .x0 .x19, .movz .x .x2 1 0, mov .x3 .x20]) (.call "vg_sha256_compress" compress)

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 32
  so := 112
  len := MdStream.AArch64.len64 88 true
  out := MdStream.AArch64.out32 8 true

def update : Prog isa := MdStream.AArch64.update params "vg_sha256_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_sha256_compress" compress

end VG.Impl.Sha256.AArch64.Stream
