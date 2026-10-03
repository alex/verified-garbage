import VerifiedGarbage.Impl.Md5.Arm
import VerifiedGarbage.Impl.MdStream.Arm

/-!
# Streaming MD5: 32-bit ARM implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`).

* `init(state = r0)` stores the initial MD buffer.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/Arm.lean`), calling the compression function
  (`vg_md5_compress`) with `scratch[0..64)` as its scratch space, and saving our
  caller's `r4`–`r11` and `lr` in `scratch[64..100)`.
-/

namespace VG.Impl.Md5.Arm.Stream

open VG.Arm
open VG.Impl.Md5.Arm (compress)

def init : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    [.movw .r12 (Spec.Md5.H0[k]!.extractLsb' 0 16),
     .movt .r12 (Spec.Md5.H0[k]!.extractLsb' 16 16),
     .str .r12 .r0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/Arm.lean`). -/

def params : MdStream.Arm.Params where
  N := 16
  B := 64
  L := 8
  so := 64
  len := MdStream.Arm.len64 72 false
  out := MdStream.Arm.out32 4 false

def update : Prog isa := MdStream.Arm.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.Arm.finalize params "vg_md5_compress" compress

end VG.Impl.Md5.Arm.Stream
