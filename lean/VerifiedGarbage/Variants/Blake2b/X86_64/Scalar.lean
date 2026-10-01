import VerifiedGarbage.Proof.Blake2.X86_64.Backend

/-! # BLAKE2b on baseline x86-64 -/

namespace VG.Variants.Blake2b.X86_64.Scalar

def variant : Proof.Blake2.X86_64.Backend where
  suffix := ""
  features := []
  code := Impl.Blake2.X86_64.compress Spec.Blake2.b
  callee := Proof.Blake2.X86_64.Stream.calleeB
  verified := Proof.Blake2.X86_64.compressB_verified
  spSafe := Code.all_of_allInstrs (by lit_decide)
  updateCT := Proof.Blake2.X86_64.Stream.updateB_ct
  finalizeCT := Proof.Blake2.X86_64.Stream.finalizeB_ct
  updateMxcsr := by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b).allInstrs _ = true
    lit_decide
  finalizeMxcsr := by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b).allInstrs _ = true
    lit_decide
  updateSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.update Spec.Blake2.b).allInstrs _ = true
    lit_decide)
  finalizeSpSafe := Code.all_of_allInstrs (by
    change (Impl.Blake2.X86_64.Stream.finalize Spec.Blake2.b).allInstrs _ = true
    lit_decide)

end VG.Variants.Blake2b.X86_64.Scalar
