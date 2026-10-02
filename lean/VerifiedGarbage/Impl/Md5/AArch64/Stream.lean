import VerifiedGarbage.Impl.Md5.AArch64
import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# Streaming MD5: AArch64 implementation

The streaming state (80 bytes at `state`) is the MD buffer followed by a
64-byte buffer (see `VG.Spec.Md5.Repr`).

* `init(state = x0)` stores the initial MD buffer.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_md5_compress`).
-/

namespace VG.Impl.Md5.AArch64.Stream

open VG.AArch64
open VG.Impl.Md5.AArch64 (compress)

def init : Prog isa :=
  .block ((List.range 4).flatMap fun k =>
    [.movz .w .x9 (Spec.Md5.H0[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Md5.H0[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 16
  B := 64
  L := 8
  so := 64
  len := MdStream.AArch64.len64 72 false
  out := MdStream.AArch64.out32 4 false

def update : Prog isa := MdStream.AArch64.update params "vg_md5_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_md5_compress" compress

end VG.Impl.Md5.AArch64.Stream
