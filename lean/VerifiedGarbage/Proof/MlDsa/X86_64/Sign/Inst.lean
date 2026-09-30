import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT

/-!
# ML-DSA signing on x86-64: the primitives it calls

Untrusted: everything here is checked by Lean. The verified x86-64
implementations of the primitives (`prims`), and what the proofs of signing
need of them (`prims_ok`), with 24 bytes of stack for each call: their
contracts, and, of the two samplers whose result signing branches on, that
it depends only on their public data and that they succeed only if the
algorithm finishes within `maxBounds` (from what their own proofs say they
return, `rejNTT_correct` and `sampleInBall_correct`).
-/

namespace VG.Proof.MlDsa.X86_64.Sign

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The x86-64 implementations of the primitives. -/
def prims : Prims where
  ntt := Impl.MlDsa.X86_64.Arith.ntt
  invNtt := Impl.MlDsa.X86_64.Arith.nttInv
  mul := Impl.MlDsa.X86_64.Arith.mul
  mulAdd := Impl.MlDsa.X86_64.Arith.mulAdd
  add := Impl.MlDsa.X86_64.Arith.add
  sub := Impl.MlDsa.X86_64.Arith.sub
  rejNTT := Impl.MlDsa.X86_64.Sample.rejNTT
  expandMask := Impl.MlDsa.X86_64.Sample.expandMask
  ball := Impl.MlDsa.X86_64.Sample.sampleInBall
  highBits := Impl.MlDsa.X86_64.Round.highBits
  lowBits := Impl.MlDsa.X86_64.Round.lowBits
  normLt := Impl.MlDsa.X86_64.Round.normLt
  makeHint := Impl.MlDsa.X86_64.Round.makeHint
  simpleBitPack := Impl.MlDsa.X86_64.Pack.simpleBitPack
  bitPack := Impl.MlDsa.X86_64.Pack.bitPack
  bitUnpack := Impl.MlDsa.X86_64.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.X86_64.Pack.hintBitPack

theorem nosp_of {c : Prog isa} (h : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true) : NoSp c := by
  rw [Code.allInstrs_eq] at h
  intro i hi
  simpa using List.all_eq_true.mp h i hi

/-- The stack signing gives each call. -/
abbrev signStack : Nat := 24

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.X86_64.Sample VG.Proof.MlDsa.Sample

theorem rn_pre (s : State) (h : (rejNTTContract X86_64.abi 16).pre s) : rnK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs]

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract X86_64.abi 16).pub s₁ s₂) :
    bytesAt s₁.mem (s₁.gpr .rdi) 34 = bytesAt s₂.mem (s₂.gpr .rdi) 34 := by
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, rnK, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨_, hb, hdi, _, _⟩ := h
  exact VG.Proof.MlDsa.Sign.leakBytes_inj hb

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract X86_64.abi 16).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.rejNTT s tr s') :
    (s'.gpr .rax).setWidth 32 =
      if (rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := rejNTT_correct s (rn_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

theorem sb_pre (s : State) (h : (sampleInBallContract X86_64.abi 16).pre s) : sbK.pre s := by
  revert s h
  sig_implies_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi, X86_64.argRegs]

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract X86_64.abi 16).pub s₁ s₂) :
    tauOf s₁ = tauOf s₂ ∧
      bytesAt s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat = bytesAt s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat := by
  sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, sbK, X86_64.abi, X86_64.argRegs] at h
  obtain ⟨_, hb, _, _, hdx, _, _⟩ := h
  exact ⟨by rw [tauOf, tauOf, hdx], VG.Proof.MlDsa.Sign.leakBytes_inj hb⟩

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract X86_64.abi 16).pre s)
    (e : Exec isa Impl.MlDsa.X86_64.Sample.sampleInBall s tr s') :
    (s'.gpr .rax).setWidth 32 =
      if (ballFold (tauOf s) (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', _, hq⟩ := sampleInBall_correct s (sb_pre s h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact hq.1

end

theorem one_ne_zero32 : (1 : BitVec 32) ≠ 0 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
def prims_ok : PrimsOk prims signStack where
  ntt := ⟨0, by decide, Proof.MlDsa.X86_64.Arith.ntt_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  invNtt := ⟨0, by decide, Proof.MlDsa.X86_64.Arith.nttInv_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  mul := ⟨0, by decide, Proof.MlDsa.X86_64.Arith.mul_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  mulAdd := ⟨0, by decide, Proof.MlDsa.X86_64.Arith.mulAdd_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  add := ⟨0, by decide, Proof.MlDsa.X86_64.Arith.add_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  sub := ⟨0, by decide, Proof.MlDsa.X86_64.Arith.sub_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  rejNTT := ⟨16, by decide, Proof.MlDsa.X86_64.Sample.rejNTT_verified, nosp_of (by decide +kernel),
    by decide +kernel⟩
  expandMask := ⟨16, by decide, Proof.MlDsa.X86_64.Sample.expandMask_verified, nosp_of (by decide +kernel),
    by decide +kernel⟩
  ball := ⟨16, by decide, Proof.MlDsa.X86_64.Sample.sampleInBall_verified, nosp_of (by decide +kernel),
    by decide +kernel⟩
  highBits := ⟨0, by decide, Proof.MlDsa.X86_64.Round.highBits_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  lowBits := ⟨0, by decide, Proof.MlDsa.X86_64.Round.lowBits_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  normLt := ⟨0, by decide, Proof.MlDsa.X86_64.Round.normLt_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  makeHint := ⟨0, by decide, Proof.MlDsa.X86_64.Round.makeHint_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  simpleBitPack := ⟨0, by decide, Proof.MlDsa.X86_64.Pack.simpleBitPack_verified, nosp_of (by decide +kernel),
    by decide +kernel⟩
  bitPack := ⟨0, by decide, Proof.MlDsa.X86_64.Pack.bitPack_verified, nosp_of (by decide +kernel), by decide +kernel⟩
  bitUnpack := ⟨0, by decide, Proof.MlDsa.X86_64.Pack.bitUnpack_verified, nosp_of (by decide +kernel),
    by decide +kernel⟩
  hintBitPack := ⟨0, by decide, Proof.MlDsa.X86_64.Pack.hintBitPack_verified, nosp_of (by decide +kernel),
    by decide +kernel⟩
  rejRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.X86_64.Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩
  rejMax := fun s t s' h e h1 => by
    rw [rn_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (G (bytesAt s.mem (s.gpr .rdi) 34) 1008)).length = 256
    · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (VG.Proof.MlDsa.Sample.rejNTT_some hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32
  ballRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.X86_64.Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩
  ballMax := fun s t s' h e h1 => by
    rw [sb_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.ballFold (VG.Proof.MlDsa.X86_64.Sample.tauOf s)
      (H (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 272)).2 = 256
    · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (VG.Proof.MlDsa.Sample.sampleInBall_some _ (by decide) hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32
  hD := by decide
  hD' := by decide

end VG.Proof.MlDsa.X86_64.Sign
