import VerifiedGarbage.Impl.Sha1.AArch64
import VerifiedGarbage.Impl.MdStream.AArch64

/-!
# Streaming SHA-1: AArch64 implementation

The streaming state (84 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha1.Repr`).

* `init(state = x0)` stores the initial hash value.
* `update` and `finalize` are the generic streaming code
  (`Impl/MdStream/AArch64.lean`), calling the compression function
  (`vg_sha1_compress`).
-/

namespace VG.Impl.Sha1.AArch64.Stream

open VG.AArch64
open VG.Impl.Sha1.AArch64 (compress)

def init : Prog isa :=
  .block ((List.range 5).flatMap fun k =>
    [.movz .w .x9 (Spec.Sha1.H0[k]!.extractLsb' 0 16) 0,
     .movk .w .x9 (Spec.Sha1.H0[k]!.extractLsb' 16 16) 1,
     .str .w .x9 .x0 (4 * k)])

/-! ## `update` and `finalize`

The generic streaming code (`Impl/MdStream/AArch64.lean`). -/

def params : MdStream.AArch64.Params where
  N := 20
  B := 64
  L := 8
  so := 112
  len := MdStream.AArch64.len64 76 true
  out := MdStream.AArch64.out32 5 true

def update : Prog isa := MdStream.AArch64.update params "vg_sha1_compress" compress

def finalize : Prog isa := MdStream.AArch64.finalize params "vg_sha1_compress" compress

end VG.Impl.Sha1.AArch64.Stream
