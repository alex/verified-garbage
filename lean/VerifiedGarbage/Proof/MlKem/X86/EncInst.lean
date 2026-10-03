import VerifiedGarbage.Proof.MlKem.X86.EncV

/-!
# ML-KEM-768 on x86 (32-bit): the layout of K-PKE.Encrypt

The facts of the layout of `scratch` that the proof of `encrypt`
(`Enc*.lean`) uses, for ML-KEM-768 (`L768`), computed from its offsets.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86.Top

instance : BaseOK L768 where
  n hS := by sc_decide
  rn hS := by sc_decide
  hash hS := by sc_decide

instance : YOK L768 where
  y hS := by sc_decide
  acc hS := by sc_decide

instance : EntOK L768 where
  seed hS := by sc_decide
  ent hS := by sc_decide'
  mul hS := by sc_decide'

instance : RowOK L768 where
  row hS := by sc_decide'

instance : VOK L768 where
  v hS := by sc_decide'
  w hS := by sc_decide'
  ct hS := by sc_decide

end VG.Proof.MlKem.X86.Enc
