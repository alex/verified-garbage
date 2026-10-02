import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.Ball

/-!
# ML-DSA signing on AArch64: the primitives it calls

The verified AArch64 implementations of the primitives (`prims`), and what the
proofs of signing need of them (`prims_ok`), with 16 bytes of stack for each
call (the samplers' frames): their contracts (`CalleeOk.of_verified`), and, of
the two samplers whose result signing branches on, that it depends only on
their public data and that they succeed only if the algorithm finishes within
`maxBounds` (from what their own proofs say they return, `RejNtt.correct` and
`Ball.correct`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The AArch64 implementations of the primitives. -/
def primsWith (c : Impl.Sha3.AArch64.Callee) : Prims where
  suffix := c.suffix
  ntt := Impl.MlDsa.AArch64.Arith.ntt
  invNtt := Impl.MlDsa.AArch64.Arith.nttInv
  mul := Impl.MlDsa.AArch64.Arith.mul
  mulAdd := Impl.MlDsa.AArch64.Arith.mulAdd
  add := Impl.MlDsa.AArch64.Arith.add
  sub := Impl.MlDsa.AArch64.Arith.sub
  rejNTT := Impl.MlDsa.AArch64.Sample.rejNTTWith c
  expandMask := Impl.MlDsa.AArch64.Sample.expandMaskWith c
  ball := Impl.MlDsa.AArch64.Sample.sampleInBallWith c
  highBits := Impl.MlDsa.AArch64.Round.highBits
  lowBits := Impl.MlDsa.AArch64.Round.lowBits
  normLt := Impl.MlDsa.AArch64.Round.normLt
  makeHint := Impl.MlDsa.AArch64.Round.makeHint
  simpleBitPack := Impl.MlDsa.AArch64.Pack.simpleBitPack
  bitPack := Impl.MlDsa.AArch64.Pack.bitPack
  bitUnpack := Impl.MlDsa.AArch64.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.AArch64.Pack.hintBitPack

def prims := primsWith .scalar

/-- The stack signing gives each call. -/
abbrev signStack : Nat := 16

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.AArch64.Sample VG.Proof.MlDsa.Sample

theorem rn_pre (s : State) (h : (rejNTTContract AArch64.abi 16).pre s) : rnK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs]

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract AArch64.abi 16).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .x0) 34 = bytesAt s₂.mem (s₂.gpr .x0) 34 := by
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, AArch64.abi, AArch64.argRegs] at h
  obtain ⟨_, hb, _⟩ := h
  exact Proof.MlKem.AArch64.Sample.map_toNat_inj hb

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract AArch64.abi 16).pre s)
    (e : Exec isa (Impl.MlDsa.AArch64.Sample.rejNTTWith keccak.callee) s tr s') :
    (s'.gpr .x0).setWidth 32 =
      if (rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := RejNtt.correctWith keccak s (rn_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

theorem sb_pre (s : State) (h : (sampleInBallContract AArch64.abi 16).pre s) : sbK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi, AArch64.argRegs]

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract AArch64.abi 16).pub s₁ s₂) :
    tauOf s₁ = tauOf s₂ ∧
      bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat = bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat := by
  sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, AArch64.abi, AArch64.argRegs] at h
  obtain ⟨_, hb, _, _, hx2, _, _⟩ := h
  exact ⟨by rw [tauOf, tauOf, hx2], Proof.MlKem.AArch64.Sample.map_toNat_inj hb⟩

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract AArch64.abi 16).pre s)
    (e : Exec isa (Impl.MlDsa.AArch64.Sample.sampleInBallWith keccak.callee) s tr s') :
    (s'.gpr .x0).setWidth 32 =
      if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := Ball.correctWith keccak s (sb_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

end

theorem one_ne_zero32 : (1 : BitVec 32) ≠ 0 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
theorem prims_okWith : PrimsOk (primsWith keccak.callee) signStack where
  s16 := by decide
  sl := by decide
  ntt := by
    have h := Proof.MlDsa.AArch64.Arith.ntt_verified
    unfold Spec.MlDsa.nttContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [primsWith]; decide +kernel)
  invNtt := by
    have h := Proof.MlDsa.AArch64.Arith.nttInv_verified
    unfold Spec.MlDsa.nttInvContract at h ⊢
    exact CalleeOk.of_verified (by decide) h (by decide) (by dsimp only [primsWith]; decide +kernel)
  mul := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Arith.mul_verified (by decide) (by dsimp only [primsWith]; decide +kernel)
  mulAdd := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Arith.mulAdd_verified (by decide) (by dsimp only [primsWith]; decide +kernel)
  add := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Arith.add_verified (by decide) (by dsimp only [primsWith]; decide +kernel)
  sub := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Arith.sub_verified (by decide) (by dsimp only [primsWith]; decide +kernel)
  rejNTT := CalleeOk.of_verified (S := signStack) (by decide) (Proof.MlDsa.AArch64.Sample.rejNTT_verifiedWith keccak) (by decide)
    (by simp [primsWith, signStack, Sample.rejNTT_depth keccak])
  expandMask := CalleeOk.of_verified (S := signStack) (by decide) (Proof.MlDsa.AArch64.Sample.expandMask_verifiedWith keccak) (by decide)
    (by simp [primsWith, signStack, Sample.expandMask_depth keccak])
  ball := CalleeOk.of_verified (S := signStack) (by decide) (Proof.MlDsa.AArch64.Sample.sampleInBall_verifiedWith keccak) (by decide)
    (by simp [primsWith, signStack, Sample.ball_depth keccak])
  highBits := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Round.highBits_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  lowBits := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Round.lowBits_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  normLt := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Round.normLt_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  makeHint := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Round.makeHint_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  simpleBitPack := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Pack.simpleBitPack_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  bitPack := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Pack.bitPack_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  bitUnpack := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Pack.bitUnpack_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  hintBitPack := CalleeOk.of_verified (S := signStack) (by decide) Proof.MlDsa.AArch64.Pack.hintBitPack_verified (by decide)
    (by dsimp only [primsWith]; decide +kernel)
  rejRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨(Proof.MlDsa.AArch64.Sample.rejNTT_verifiedWith keccak).2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩
  rejMax := fun s t s' h e h1 => by
    rw [rn_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (G (bytesAt s.mem (s.gpr .x0) 34) 1008)).length = 256
    · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (VG.Proof.MlDsa.Sample.rejNTT_some hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32
  ballRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨(Proof.MlDsa.AArch64.Sample.sampleInBall_verifiedWith keccak).2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩
  ballMax := fun s t s' h e h1 => by
    rw [sb_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.ballFold (VG.Proof.MlDsa.AArch64.Sample.tauOf s)
      (H (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) 272)).2 = 256
    · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide)
        (VG.Proof.MlDsa.Sample.sampleInBall_some _ (by decide) hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32

theorem prims_ok : PrimsOk prims signStack := prims_okWith (keccak := .scalar)

end VG.Proof.MlDsa.AArch64.Sign
