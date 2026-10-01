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
  absorbKeeps : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
    ∀ i ∈ instrs (Impl.Sha3.AArch64.Stream.absorbMainWith callee), dstOf i ≠ some r
  squeezeKeeps : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
    ∀ i ∈ instrs (Impl.Sha3.AArch64.Stream.squeezeMainWith callee), dstOf i ≠ some r
  absorbTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.absorbWith callee) h).isSome = true
  padTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x4])
    (Impl.Sha3.AArch64.Stream.padWith callee) h).isSome = true
  squeezeTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
    (Impl.Sha3.AArch64.Stream.squeezeWith callee) h).isSome = true

  sampleFullTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeWith callee) h).isSome = true
  sampleFastTaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2])
    (Impl.MlKem.AArch64.sampleSqueezeNWith callee 504 (Impl.MlKem.AArch64.sampleRegs 168)) h).isSome = true

  mldsaNttTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 168 1008) h).isSome = true
  mldsaBoundedTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 544) h).isSome = true
  mldsaBallTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.spongeWith callee 136 272) h).isSome = true
  mldsaMaskTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x3, .x4])
    (Impl.MlDsa.AArch64.Sample.expandMaskTailWith callee) h).isSome = true

  mlkemKgATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.kgAWith callee) h).isSome = true
  mlkemKgCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.kgCWith callee) h).isSome = true

  mlkemEnATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem.AArch64.enAWith callee) h).isSome = true

  mlkemEnCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.enCWith callee) h).isSome = true

  mlkemDeATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem.AArch64.deAWith callee) h).isSome = true

  mlkemDeCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem.AArch64.deCWith callee) h).isSome = true

  mlkem1024KgATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.kgAWith callee) h).isSome = true

  mlkem1024KgCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.kgCWith callee) h).isSome = true

  mlkem1024EnATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4])
    (Impl.MlKem1024.AArch64.enAWith callee) h).isSome = true

  mlkem1024EnCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.enCWith callee) h).isSome = true

  mlkem1024DeATaint : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (Impl.MlKem1024.AArch64.deAWith callee) h).isSome = true

  mlkem1024DeCTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlKem1024.AArch64.deCWith callee) h).isSome = true

  mldsaSeedsTaint : ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x25, 0, 32⟩, ⟨.x28, 896, 2⟩] [⟨.x28, 1024, 128⟩]) h).isSome = true
  mldsaTrHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.trHashWith callee p) h).isSome = true
  mldsaVerifyHashTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (taint.check (Taint.ofRegs [.x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.KeyGen.shake256With callee [⟨.x26, 0, 64⟩,
      ⟨.x28, (Impl.MlDsa.AArch64.Verify.bP p).2, p.k * Impl.MlDsa.AArch64.Verify.w1Len p⟩]
      [⟨.x28, 1024, p.ctildeLen⟩]) h).isSome = true

  mldsaSignDecodeTaint : ∃ h, (taint.check (Taint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x25, 32, 32⟩, ⟨.x27, 0, 32⟩, ⟨.x26, 0, 64⟩] ⟨.x28, 960, 64⟩) h).isSome = true
  mldsaSignCommitTaint : ∀ p : Spec.MlDsa.Params,
    (p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) → ∃ h, (taint.check (Taint.ofRegs [.x23, .x25, .x26, .x27, .x28])
    (Impl.MlDsa.AArch64.Sign.shakeAtWith callee [⟨.x26, 0, 64⟩,
      ⟨.x28, 2048, p.k * Impl.MlDsa.AArch64.Sign.w1Len p⟩]
      ⟨.x28, 1040, Impl.MlDsa.AArch64.Sign.cLen p⟩) h).isSome = true

theorem fdepth_of_noFrames {c : Prog isa} (h : c.noFrames = true) : c.fdepth = 0 := by
  induction c <;> simp_all [Code.noFrames, Code.fdepth]

theorem Permutation.absorbMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbMainWith v.callee).fdepth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.absorbMainWith, Impl.Sha3.AArch64.Stream.absorbBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.fdepth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.absorb_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.absorbWith v.callee).fdepth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.absorbWith, Code.fdepth, v.absorbMain_depth]

theorem Permutation.padMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.padMainWith v.callee).fdepth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.padMainWith, Code.fdepth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.pad_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.padWith v.callee).fdepth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.padWith, Code.fdepth, v.padMain_depth]

theorem Permutation.squeezeMain_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeMainWith v.callee).fdepth = 0 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeMainWith, Impl.Sha3.AArch64.Stream.squeezeBodyWith, Impl.Sha3.AArch64.Stream.permuteAtWith, Code.fdepth,
    fdepth_of_noFrames v.noFrames, Nat.max_self]

theorem Permutation.squeeze_depth (v : Permutation) :
    (Impl.Sha3.AArch64.Stream.squeezeWith v.callee).fdepth = 1 := by
  simp only [Impl.Sha3.AArch64.Stream.squeezeWith, Code.fdepth, v.squeezeMain_depth]

theorem keeps_of_check {c : Prog isa} {rs : List Reg}
    (h : (c.allInstrs fun i => rs.all fun r => dstOf i != some r) = true) :
    ∀ r ∈ rs, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  rw [Code.allInstrs_eq] at h
  intro r hr i hi
  have h' := List.all_eq_true.mp (List.all_eq_true.mp h i hi) r hr
  simpa using h'

def Permutation.scalar : Permutation where
  callee := .scalar
  features := []
  ok := permute_correct
  noFrames := permute_noFrames
  absorbKeeps := keeps_of_check (by decide +kernel)
  squeezeKeeps := keeps_of_check (by decide +kernel)
  absorbTaint := ⟨_, by taint_decide⟩
  padTaint := ⟨_, by taint_decide⟩
  squeezeTaint := ⟨_, by taint_decide⟩
  sampleFullTaint := ⟨_, by taint_decide⟩
  sampleFastTaint := ⟨_, by taint_decide⟩
  mldsaNttTaint := ⟨_, by taint_decide⟩
  mldsaBoundedTaint := ⟨_, by taint_decide⟩
  mldsaBallTaint := ⟨_, by taint_decide⟩
  mldsaMaskTaint := ⟨_, by taint_decide⟩
  mlkemKgATaint := ⟨_, by taint_decide⟩
  mlkemKgCTaint := ⟨_, by taint_decide⟩
  mlkemEnATaint := ⟨_, by taint_decide⟩
  mlkemEnCTaint := ⟨_, by taint_decide⟩
  mlkemDeATaint := ⟨_, by taint_decide⟩
  mlkemDeCTaint := ⟨_, by taint_decide⟩
  mlkem1024KgATaint := ⟨_, by taint_decide⟩
  mlkem1024KgCTaint := ⟨_, by taint_decide⟩
  mlkem1024EnATaint := ⟨_, by taint_decide⟩
  mlkem1024EnCTaint := ⟨_, by taint_decide⟩
  mlkem1024DeATaint := ⟨_, by taint_decide⟩
  mlkem1024DeCTaint := ⟨_, by taint_decide⟩

  mldsaSeedsTaint := ⟨_, by taint_decide⟩
  mldsaTrHashTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩
  mldsaVerifyHashTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

  mldsaSignDecodeTaint := ⟨_, by taint_decide⟩
  mldsaSignCommitTaint := by
    intro p hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

end VG.Proof.Sha3.AArch64
