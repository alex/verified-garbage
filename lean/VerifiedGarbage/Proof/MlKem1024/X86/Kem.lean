import VerifiedGarbage.Proof.MlKem.X86.EncV
import VerifiedGarbage.Proof.MlKem1024.X86.CompressEncode
import VerifiedGarbage.Proof.MlKem1024.X86.DecodeDecompress
import VerifiedGarbage.Impl.MlKem1024.X86.Kem

/-!
# ML-KEM-1024 on x86 (32-bit): the parameter set

ML-KEM-1024's layout (`L1024`) compresses to 11 and 5 bits with
`vg_mlkem1024_compress_encode` and `vg_mlkem1024_decode_decompress` (`CeOK`),
and has the facts of the layout of K-PKE.Encrypt that its proof
(`Proof/MlKem/X86/Enc*.lean`) uses, computed from its offsets.
-/

namespace VG.Proof.MlKem1024.X86

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top

theorem ce1024 : CeFn Impl.MlKem1024.X86.compressEncode Spec.MlKem1024.compressWidths :=
  ⟨CompressEncode.verified, NoSp.of_all (by decide +kernel), by decide +kernel, by decide⟩

theorem dd1024 : DdFn Impl.MlKem1024.X86.decodeDecompress Spec.MlKem1024.compressWidths :=
  ⟨DecodeDecompress.verified, NoSp.of_all (by decide +kernel), by decide +kernel, by decide⟩

instance : CeOK L1024 := ⟨⟨_, by decide, by decide, ce1024⟩, ⟨_, by decide, by decide, dd1024⟩⟩

end VG.Proof.MlKem1024.X86

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem.X86.Top

instance : BaseOK L1024 where
  n hS := by sc_decide
  rn hS := by sc_decide
  hash hS := by sc_decide

instance : YOK L1024 where
  y hS := by sc_decide
  acc hS := by sc_decide

instance : EntOK L1024 where
  seed hS := by sc_decide
  ent hS := by sc_decide'
  mul hS := by sc_decide'

instance : RowOK L1024 where
  row hS := by sc_decide'

instance : VOK L1024 where
  v hS := by sc_decide'
  w hS := by sc_decide'
  ct hS := by sc_decide

end VG.Proof.MlKem.X86.Enc
