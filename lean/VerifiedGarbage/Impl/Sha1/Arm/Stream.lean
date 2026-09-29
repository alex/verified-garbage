import VerifiedGarbage.Impl.Sha1.Arm
import VerifiedGarbage.Impl.MdStream.Arm

/-!
# Streaming SHA-1: 32-bit ARM implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`).

* `init(state = r0)` stores the initial hash value.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_sha1_compress`) with `scratch[0..112)` as its scratch space, and saving our
  caller's `r4`–`r11` and `lr` in `scratch[112..148)`.
-/

namespace VG.Impl.Sha1.Arm.Stream

open VG.Arm
open VG.Impl.Sha1.Arm (compress)

def init : Prog isa :=
  .block ((List.range 5).flatMap fun k =>
    [.movw .r12 (Spec.Sha1.H0[k]!.extractLsb' 0 16),
     .movt .r12 (Spec.Sha1.H0[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/Arm.lean`). -/

def params : MdStream.Arm.Params where
  N := 20
  so := 112
  len := MdStream.Arm.len64 76 true
  out := MdStream.Arm.out32 5 true

def update : Prog isa := MdStream.Arm.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_sha1_compress" compress

end VG.Impl.Sha1.Arm.Stream
