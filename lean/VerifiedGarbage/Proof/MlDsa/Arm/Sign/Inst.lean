import VerifiedGarbage.Proof.MlDsa.Arm.Sign.SignCT
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.Arm.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.Arm.Round.Bits
import VerifiedGarbage.Proof.MlDsa.Arm.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.Arm.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.BitPack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.Arm.Pack.HintPackCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.Arm.Sample.BallCT

/-!
# ML-DSA signing on ARMv7: the primitives it calls

The verified ARMv7 implementations of the primitives (`prims`), and what the
proofs of signing need of them (`prims_ok`), with 28 bytes of stack below the
function's stack pointer: their contracts with the stack of their
registrations (at most 28 bytes, or 20 for the four whose fifth argument
signing pushes), that their frames fit in it, and, of the two samplers whose
result signing branches on, that it depends only on their public data and that
they succeed only if the algorithm finishes within `maxBounds` (from what
their own proofs say they return).
-/

namespace VG.Proof.MlDsa.Arm.Sign

open VG VG.Arm VG.Impl.MlDsa.Arm.Sign
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The ARMv7 implementations of the primitives. -/
def prims : Prims where
  ntt := Impl.MlDsa.Arm.Arith.ntt
  invNtt := Impl.MlDsa.Arm.Arith.nttInv
  mul := Impl.MlDsa.Arm.Arith.mul
  mulAdd := Impl.MlDsa.Arm.Arith.mulAdd
  add := Impl.MlDsa.Arm.Arith.add
  sub := Impl.MlDsa.Arm.Arith.sub
  rejNTT := Impl.MlDsa.Arm.Sample.rejNTT
  expandMask := Impl.MlDsa.Arm.Sample.expandMask
  ball := Impl.MlDsa.Arm.Sample.sampleInBall
  highBits := Impl.MlDsa.Arm.Round.highBits
  lowBits := Impl.MlDsa.Arm.Round.lowBits
  normLt := Impl.MlDsa.Arm.Round.normLt
  makeHint := Impl.MlDsa.Arm.Round.makeHint
  simpleBitPack := Impl.MlDsa.Arm.Pack.simpleBitPack
  bitPack := Impl.MlDsa.Arm.Pack.bitPack
  bitUnpack := Impl.MlDsa.Arm.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.Arm.Pack.hintBitPack

/-- The stack signing may use below its stack pointer. -/
abbrev signStack : Nat := 28

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.Arm.Sample VG.Proof.MlDsa.Sample

theorem rn_ret {s s' : State} {tr : List Leak} (h : (rejNTTContract Arm.abi 8).pre s)
    (e : Exec isa Impl.MlDsa.Arm.Sample.rejNTT s tr s') :
    s'.gpr .r0 = if (rnFold [] (G (bytesAt s.mem (State.addr (s.gpr .r0)) 34) 1008)).length = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := RejNtt.correct (RejNtt.spOk_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem rn_pub (s₁ s₂ : State) (h : (rejNTTContract Arm.abi 8).pub s₁ s₂) :
    bytesAt s₁.mem (State.addr (s₁.gpr .r0)) 34 = bytesAt s₂.mem (State.addr (s₂.gpr .r0)) 34 := by
  sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨_, hb, _⟩ := h
  exact VG.Proof.MlDsa.Sign.leakBytes_inj hb

theorem sb_ret {s s' : State} {tr : List Leak} (h : (sampleInBallContract Arm.abi 8).pre s)
    (e : Exec isa Impl.MlDsa.Arm.Sample.sampleInBall s tr s') :
    s'.gpr .r0 = if (ballFold (s.gpr .r2).toNat
      (H (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 272)).2 = 256 then 1 else 0 := by
  obtain ⟨_, _, e', h0, _⟩ := Ball.correct (Ball.pre_of h)
  obtain ⟨-, rfl⟩ := Exec.det e e'
  exact h0

theorem sb_pub (s₁ s₂ : State) (h : (sampleInBallContract Arm.abi 8).pub s₁ s₂) :
    s₁.gpr .r2 = s₂.gpr .r2 ∧ bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (s₁.gpr .r1).toNat =
      bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (s₂.gpr .r1).toNat := by
  sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨_, hb, _, _, h2, _⟩ := h
  exact ⟨h2, (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩

end

theorem one_ne_zero32 : (1 : BitVec 32) ≠ 0 := by decide

/-- The primitives satisfy what the proofs of signing need of them. -/
def prims_ok : PrimsOk prims signStack where
  ntt := ⟨28, by decide, Proof.MlDsa.Arm.Arith.Ntt.verified, by decide +kernel⟩
  invNtt := ⟨28, by decide, Proof.MlDsa.Arm.Arith.NttInv.verified, by decide +kernel⟩
  mul := ⟨24, by decide, Proof.MlDsa.Arm.Arith.Mul.mul_verified, by decide +kernel⟩
  mulAdd := ⟨24, by decide, Proof.MlDsa.Arm.Arith.Mul.mulAdd_verified, by decide +kernel⟩
  add := ⟨0, by decide, Proof.MlDsa.Arm.Arith.AddSub.add_verified, by decide +kernel⟩
  sub := ⟨0, by decide, Proof.MlDsa.Arm.Arith.AddSub.sub_verified, by decide +kernel⟩
  rejNTT := ⟨8, by decide, Proof.MlDsa.Arm.Sample.rejNTT_verified, by decide +kernel⟩
  expandMask := ⟨8, by decide, Proof.MlDsa.Arm.Sample.expandMask_verified, by decide +kernel⟩
  ball := ⟨8, by decide, Proof.MlDsa.Arm.Sample.sampleInBall_verified, by decide +kernel⟩
  highBits := ⟨0, by decide, Proof.MlDsa.Arm.Round.Bits.high_verified, by decide +kernel⟩
  lowBits := ⟨0, by decide, Proof.MlDsa.Arm.Round.Bits.low_verified, by decide +kernel⟩
  normLt := ⟨4, by decide, Proof.MlDsa.Arm.Round.NormLt.verified, by decide +kernel⟩
  makeHint := ⟨12, by decide, Proof.MlDsa.Arm.Round.MakeHint.verified, by decide +kernel⟩
  simpleBitPack := ⟨0, by decide, Proof.MlDsa.Arm.Pack.simpleBitPack_verified, by decide +kernel⟩
  bitPack := ⟨4, by decide, Proof.MlDsa.Arm.Pack.bitPack_verified, by decide +kernel⟩
  bitUnpack := ⟨4, by decide, Proof.MlDsa.Arm.Pack.bitUnpack_verified, by decide +kernel⟩
  hintBitPack := ⟨8, by decide, Proof.MlDsa.Arm.Pack.Hint.hintBitPack_verified, by decide +kernel⟩
  rejRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.Arm.Sample.rejNTT_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [rn_ret h₁ e₁, rn_ret h₂ e₂, rn_pub s₁ s₂ hp]⟩
  rejMax := fun s t s' h e h1 => by
    rw [rn_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.rnFold [] (G (bytesAt s.mem (State.addr (s.gpr .r0)) 34) 1008)).length = 256
    · rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (VG.Proof.MlDsa.Sample.rejNTT_some hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32
  ballRet := fun s₁ s₂ t₁ t₂ s₁' s₂' ⟨h₁, h₂, hp⟩ e₁ e₂ =>
    ⟨Proof.MlDsa.Arm.Sample.sampleInBall_verified.2.1 s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂,
      show _ = _ by rw [sb_ret h₁ e₁, sb_ret h₂ e₂, (sb_pub s₁ s₂ hp).1, (sb_pub s₁ s₂ hp).2]⟩
  ballMax := fun s t s' h e h1 => by
    rw [sb_ret h e] at h1
    by_cases hf : (VG.Proof.MlDsa.Sample.ballFold (s.gpr .r2).toNat
      (H (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 272)).2 = 256
    · rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide)
        (VG.Proof.MlDsa.Sample.sampleInBall_some _ (by decide) hf)]; rfl
    · rw [ifn hf] at h1; exact absurd h1.symm one_ne_zero32
  hD := by decide
  hD' := by decide

end VG.Proof.MlDsa.Arm.Sign
