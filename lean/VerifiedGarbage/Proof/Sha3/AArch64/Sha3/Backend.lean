import VerifiedGarbage.Proof.Sha3.AArch64.Variant
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.Permute

namespace VG.Proof.Sha3.AArch64.Sha3

open VG VG.AArch64

def callee : Impl.Sha3.AArch64.Callee :=
  ⟨"vg_keccak_f1600_sha3", Impl.Sha3.AArch64.Sha3.Hybrid.permute, "_sha3"⟩

theorem absorbTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem padTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem squeezeTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sampleFullTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem sampleFastTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mldsaNttTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mldsaBoundedTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 544) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mldsaBallTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mldsaMaskTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkemKgATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkemKgCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkemEnATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkemEnCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkemDeATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkemDeCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkem1024KgATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkem1024KgCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkem1024EnATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkem1024EnCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkem1024DeATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mlkem1024DeCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith callee) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mldsaSeedsTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem mldsaSignDecodeTaint : ∃ h, (taint.check (Taint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (taint.check (Taint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true := by
  intro p hp
  rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

def backend : Permutation where
  callee := callee
  features := ["sha3"]
  ok := Hybrid.permute_correct
  noFrames := Hybrid.permute_noFrames
  absorbKeeps := keeps_of_check (by lit_decide)
  squeezeKeeps := keeps_of_check (by lit_decide)
  absorbTaint := absorbTaint
  padTaint := padTaint
  squeezeTaint := squeezeTaint
  sampleFullTaint := sampleFullTaint
  sampleFastTaint := sampleFastTaint
  mldsaNttTaint := mldsaNttTaint
  mldsaBoundedTaint := mldsaBoundedTaint
  mldsaBallTaint := mldsaBallTaint
  mldsaMaskTaint := mldsaMaskTaint
  mlkemKgATaint := mlkemKgATaint
  mlkemKgCTaint := mlkemKgCTaint
  mlkemEnATaint := mlkemEnATaint
  mlkemEnCTaint := mlkemEnCTaint
  mlkemDeATaint := mlkemDeATaint
  mlkemDeCTaint := mlkemDeCTaint
  mlkem1024KgATaint := mlkem1024KgATaint
  mlkem1024KgCTaint := mlkem1024KgCTaint
  mlkem1024EnATaint := mlkem1024EnATaint
  mlkem1024EnCTaint := mlkem1024EnCTaint
  mlkem1024DeATaint := mlkem1024DeATaint
  mlkem1024DeCTaint := mlkem1024DeCTaint

  mldsaSeedsTaint := mldsaSeedsTaint
  mldsaTrHashTaint := mldsaTrHashTaint
  mldsaVerifyHashTaint := mldsaVerifyHashTaint

  mldsaSignDecodeTaint := mldsaSignDecodeTaint
  mldsaSignCommitTaint := mldsaSignCommitTaint

end VG.Proof.Sha3.AArch64.Sha3
