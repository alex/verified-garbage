import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.Sign
import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Impl.MlKem1024.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.Encaps
import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
import VerifiedGarbage.Impl.MlKem.AArch64.KeyGen
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.Sha3.AArch64.Permute
import VerifiedGarbage.Impl.MlKem.AArch64.Sample
import VerifiedGarbage.Proof.Sha3.AArch64.Sums

namespace VG.Proof.Sha3.AArch64

open VG VG.AArch64

/-- The permutation contract and mechanical facts needed by generic sponge callers. -/
structure Permutation where
  callee : Impl.Sha3.AArch64.Callee
  features : List String
  ok : ∀ s, Proof.Sha3.permuteAArch64.pre s →
    ∃ t s', Exec isa callee.code s t s' ∧ abiPreserved s s' ∧
      Proof.Sha3.permuteAArch64.post s s'
  noFrames : callee.code.noFrames = true
  /-- An absorb override must prove the same functional and SIMD ABI contract
  as the general loop; it need not obey that loop's syntactic register shape. -/
  absorbOverrideOk : ∀ code, callee.absorbOverride = some code →
    ∀ s, Proof.Sha3.absorbAArch64.pre s →
      ∃ t s', Exec isa code s t s' ∧ abiPreserved s s' ∧
        Proof.Sha3.absorbAArch64.post s s'
  absorbOverrideDepth : ∀ code, callee.absorbOverride = some code → code.aarch64Depth = 1
  absorbTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true
  padTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true
  squeezeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true

  sampleFullTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith callee) h).isSome = true
  sampleFastTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true

  mldsaNttTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true
  mldsaBoundedTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 544) h).isSome = true
  mldsaBallTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true
  mldsaMaskTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true

  mlkemKgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith callee) h).isSome = true
  mlkemKgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith callee) h).isSome = true

  mlkemEnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith callee) h).isSome = true

  mlkemEnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith callee) h).isSome = true

  mlkemDeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith callee) h).isSome = true

  mlkemDeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith callee) h).isSome = true

  mlkem1024KgATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith callee) h).isSome = true

  mlkem1024KgCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith callee) h).isSome = true

  mlkem1024EnATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith callee) h).isSome = true

  mlkem1024EnCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith callee) h).isSome = true

  mlkem1024DeATaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith callee) h).isSome = true

  mlkem1024DeCTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith callee) h).isSome = true

  mldsaSeedsTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true
  mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true
  mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true

  mldsaSignDecodeTaint : ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true
  mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (VectorTaint.taint.check (VectorTaint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.aarch64Depth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.aarch64Depth]

theorem Permutation.absorbMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.absorbMainWith, Impl.Sha3.AArch64.Stream.absorbBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.aarch64Depth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.absorb_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbWith v.callee).aarch64Depth = 1 := by
  cases h : v.callee.absorbOverride with
  | none =>
    simp only [Impl.Sha3.AArch64.Stream.absorbWith, h,
      Impl.Sha3.AArch64.Stream.absorbGenericWith, Code.aarch64Depth, Instr.frameUnits, v.absorbMain_depth]
  | some code =>
    simpa only [Impl.Sha3.AArch64.Stream.absorbWith, h] using v.absorbOverrideDepth code h

theorem Permutation.padMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.padMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.padMainWith, Code.aarch64Depth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.pad_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.padWith v.callee).aarch64Depth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.padWith, Code.aarch64Depth, Instr.frameUnits, v.padMain_depth]

theorem Permutation.squeezeMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeMainWith v.callee).aarch64Depth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeMainWith, Impl.Sha3.AArch64.Stream.squeezeBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.aarch64Depth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.squeeze_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeWith v.callee).aarch64Depth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeWith, Code.aarch64Depth, Instr.frameUnits, v.squeezeMain_depth]

theorem keeps_of_check {c : Prog isa} {rs : List Reg}
    (h : (c.allInstrs fun i => rs.all fun r => dstOf i != some r) = true) :
    ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  rw [Code.allInstrs_eq] at h
  intro r hr i hi
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using h'

sponge_taint_summaries ScalarSums Impl.Sha3.AArch64.Callee.scalar

def Permutation.scalar : Permutation where
  callee := .scalar
  features := []
  ok := permute_correct
  noFrames := permute_noFrames
  absorbOverrideOk := by intro code h; cases h
  absorbOverrideDepth := by intro code h; cases h
  absorbTaint := Taint.exists_check_of_sumOk_call ScalarSums.absorb (Taint.Mono.le_refl _) rfl
  padTaint := Taint.exists_check_of_sumOk_call ScalarSums.pad (Taint.Mono.le_refl _) rfl
  squeezeTaint := Taint.exists_check_of_sumOk_call ScalarSums.squeeze (Taint.Mono.le_refl _) rfl
  sampleFullTaint := by sponge_taint_decide ScalarSums
  sampleFastTaint := by sponge_taint_decide ScalarSums
  mldsaNttTaint := by sponge_taint_decide ScalarSums
  mldsaBoundedTaint := by sponge_taint_decide ScalarSums
  mldsaBallTaint := by sponge_taint_decide ScalarSums
  mldsaMaskTaint := by sponge_taint_decide ScalarSums
  mlkemKgATaint := by sponge_taint_decide ScalarSums
  mlkemKgCTaint := by sponge_taint_decide ScalarSums
  mlkemEnATaint := by sponge_taint_decide ScalarSums
  mlkemEnCTaint := by sponge_taint_decide ScalarSums
  mlkemDeATaint := by sponge_taint_decide ScalarSums
  mlkemDeCTaint := by sponge_taint_decide ScalarSums
  mlkem1024KgATaint := by sponge_taint_decide ScalarSums
  mlkem1024KgCTaint := by sponge_taint_decide ScalarSums
  mlkem1024EnATaint := by sponge_taint_decide ScalarSums
  mlkem1024EnCTaint := by sponge_taint_decide ScalarSums
  mlkem1024DeATaint := by sponge_taint_decide ScalarSums
  mlkem1024DeCTaint := by sponge_taint_decide ScalarSums

  mldsaSeedsTaint := by sponge_taint_decide ScalarSums
  mldsaTrHashTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide ScalarSums
  mldsaVerifyHashTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide ScalarSums

  mldsaSignDecodeTaint := by sponge_taint_decide ScalarSums
  mldsaSignCommitTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact by sponge_taint_decide ScalarSums

end VG.Proof.Sha3.AArch64
