import VerifiedGarbage.Proof.MlDsa.X86.Sign.Prims
import VerifiedGarbage.Proof.MlDsa.X86.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86.Round.HintF
import VerifiedGarbage.Proof.MlDsa.X86.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.X86.Sample.RejNtt
import VerifiedGarbage.Proof.MlDsa.X86.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.X86.Sample.BallTop

/-!
# ML-DSA signing on x86 (32-bit): the primitives it calls

The verified x86 implementations of the primitives (`prims`), and what the
proofs of signing need of them (`prims_ok`): their contracts, with 16 bytes of
stack (56 for the samplers); that they never write `esp`; and, of the two
samplers whose result signing branches on, what they return, from their own
proofs (`Fin` of `RejNtt.lean` and `BallTop.lean`): 1 exactly when the loop
over the output they squeeze (1008 and 272 bytes) finishes, which is within
`maxBounds`.
-/

namespace VG.Proof.MlDsa.X86.Sign

open VG VG.X86
open VG.Impl.MlDsa.X86.Sign
open VG.Proof.MlKem.X86 (Piece)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The x86 implementations of the primitives. -/
def prims : Prims where
  ntt := Impl.MlDsa.X86.Arith.ntt
  invNtt := Impl.MlDsa.X86.Arith.nttInv
  mul := Impl.MlDsa.X86.Arith.mul
  mulAdd := Impl.MlDsa.X86.Arith.mulAdd
  add := Impl.MlDsa.X86.Arith.add
  sub := Impl.MlDsa.X86.Arith.sub
  rejNTT := Impl.MlDsa.X86.Sample.rejNTT
  expandMask := Impl.MlDsa.X86.Sample.expandMask
  ball := Impl.MlDsa.X86.Sample.sampleInBall
  highBits := Impl.MlDsa.X86.Round.highBits
  lowBits := Impl.MlDsa.X86.Round.lowBits
  normLt := Impl.MlDsa.X86.Round.normLt
  makeHint := Impl.MlDsa.X86.Round.makeHint
  simpleBitPack := Impl.MlDsa.X86.Pack.simpleBitPack
  bitPack := Impl.MlDsa.X86.Pack.bitPack
  bitUnpack := Impl.MlDsa.X86.Pack.bitUnpack
  hintBitPack := Impl.MlDsa.X86.Pack.hintBitPack

/-! ## The samplers' results -/

section
open VG.Proof.MlDsa.Sample VG.Proof.MlDsa.X86.Sample

/-- Whether `vg_mldsa_rej_ntt_poly` succeeds on a seed. -/
def rejF (B : List Byte) : Bool := decide ((rnFold [] (G B 1008)).length = 256)

/-- Whether `vg_mldsa_sample_in_ball` succeeds on `τ` and a seed. -/
def ballF (τ : Nat) (B : List Byte) : Bool := decide ((ballFold τ (H B 272)).2 = 256)

theorem rej_ret (s : State) (h : (rejNTTContract X86.abi 56).pre s) (t : List Leak) (s' : State)
    (e : Exec isa Impl.MlDsa.X86.Sample.rejNTT s t s') :
    s'.gpr .eax = if rejF (bytesAt s.mem ((arg s 0).setWidth 64) 34) then 1 else 0 := by
  obtain ⟨t', s'', e', hq⟩ := RejNtt.piece.wp s s (RejNtt.Pre.of h) rfl
  obtain ⟨-, rfl⟩ := Exec.det e e'
  obtain ⟨-, -, -, sf, hfin, -, hax⟩ := hq
  have hl := hfin.len
  have eL : RejNtt.LA (RejNtt.L.Msg s) 336 = rnFold [] (G (RejNtt.L.Msg s) 1008) := by
    simp only [RejNtt.LA]; rw [List.take_of_length_le (by rw [RejNtt.X_length])]
  rw [hax, hfin.eax, eL]
  rw [eL] at hl
  show _ = if decide ((rnFold [] (G (RejNtt.L.Msg s) 1008)).length = 256) = true then 1 else 0
  by_cases e : (rnFold [] (G (RejNtt.L.Msg s) 1008)).length = 256
  · rw [e, decide_eq_true rfl]; rfl
  · rw [Nat.div_eq_of_lt (by omega), decide_eq_false e]; rfl

theorem ball_ret (s : State) (h : (sampleInBallContract X86.abi 56).pre s) (t : List Leak) (s' : State)
    (e : Exec isa Impl.MlDsa.X86.Sample.sampleInBall s t s') :
    s'.gpr .eax = if ballF (arg s 2).toNat (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) then 1 else 0 := by
  obtain ⟨t', s'', e', hq⟩ := Ball.piece.wp s s (Ball.QPre.of h) rfl
  obtain ⟨-, rfl⟩ := Exec.det e e'
  obtain ⟨-, -, -, sf, hfin, -, hax⟩ := hq
  have hl : (Ball.S' s 264).2 ≤ 256 := Ball.st_le _ _ _
  rw [hax, hfin.eax]
  rw [Ball.S'_all] at hl ⊢
  show _ = if decide ((ballFold (Ball.τ s) (H (Ball.L.Msg s) 272)).2 = 256) = true then 1 else 0
  by_cases e : (ballFold (Ball.τ s) (H (Ball.L.Msg s) 272)).2 = 256
  · rw [e, decide_eq_true rfl]; rfl
  · rw [Nat.div_eq_of_lt (by omega), decide_eq_false e]; rfl

theorem rejMax (B : List Byte) (h : rejF B = true) : (rejNTTPoly maxBounds.rejNTT B).isSome := by
  simp only [rejF, decide_eq_true_eq] at h
  rw [rejNTTPoly_mono (show 1008 ≤ maxBounds.rejNTT by decide) (rejNTT_some h)]; rfl

theorem ballMax : BallF ballF := fun τ B h => by
  simp only [ballF, decide_eq_true_eq] at h
  rw [sampleInBall_mono (show 272 ≤ maxBounds.ball by decide) (sampleInBall_some τ (by decide) h)]; rfl

end

theorem cok {c : Prog isa} (h₁ : c.allInstrs (fun i => !Taint.clobbers i .esp) = true) (h₂ : stackUse c ≤ 56) : COk c :=
  ⟨NoSp.of_all h₁, h₂⟩

/-- The primitives satisfy what the proofs of signing need of them. -/
def prims_ok : PrimsOk prims where
  ntt := Proof.MlDsa.X86.Arith.NttFwd.verified
  invNtt := Proof.MlDsa.X86.Arith.NttInvP.verified
  mul := Proof.MlDsa.X86.Arith.mul_verified
  mulAdd := Proof.MlDsa.X86.Arith.mulAdd_verified
  add := Proof.MlDsa.X86.Arith.add_verified
  sub := Proof.MlDsa.X86.Arith.sub_verified
  expandMask := Proof.MlDsa.X86.Sample.ExpandMask.verified
  highBits := Proof.MlDsa.X86.Round.highBits_verified
  lowBits := Proof.MlDsa.X86.Round.lowBits_verified
  normLt := Proof.MlDsa.X86.Round.normLt_verified
  makeHint := Proof.MlDsa.X86.Round.makeHint_verified
  simpleBitPack := Proof.MlDsa.X86.Pack.SimpleBitPack.verified
  bitPack := Proof.MlDsa.X86.Pack.BitPack.verified
  bitUnpack := Proof.MlDsa.X86.Pack.Unpack.BU.verified
  hintBitPack := Proof.MlDsa.X86.Pack.Hint.hintBitPack_verified
  rejF := rejF
  rejNTT := verified_withRet Proof.MlDsa.X86.Sample.RejNtt.verified rej_ret
  rejMax := rejMax
  ballF := ballF
  ball := verified_withRet Proof.MlDsa.X86.Sample.Ball.verified ball_ret
  ballMax := ballMax
  ok := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact cok (by decide +kernel) (by decide +kernel)

end VG.Proof.MlDsa.X86.Sign
