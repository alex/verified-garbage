import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.CTCommon
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.CTReady

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem init_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 4 0]))
      (.call Spec.Sha512.init512Api.name (Impl.Sha512.X86.Stream.init Spec.Sha512.H0_512))
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL (Proof.Sha512.X86.Stream.init_verified _).1
    (Proof.Sha512.X86.Stream.init_verified _).2.1 Whole.init_nosp (by rw [Whole.init_stack]; decide)
  · intro g m t hc hs
    apply init_ready hc hL
    exact (hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 1)⟩

theorem update_call_ct (hL : L.Ok) {vs : List Value} (hn : vs.length = 6)
    {c p n : BitVec 32} (hi : Input L p n)
    (hargs : ∀ t, OutArgs L vs t → UpdateArgs L c p n t) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L vs))
      (.call Spec.Sha512.updateApi.name Impl.Sha512.X86.Stream.update)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Update.update_verified.1
    Proof.Sha512.X86.Stream.Update.update_verified.2.1 Whole.update_nosp (by rw [Whole.update_stack])
  · intro g m t hc hs
    exact update_ready hc hL hi (hargs t hs)
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), fun j hj => call_args_eq hL (by omega) h (by omega)⟩

theorem append_pair_eq {a b c d : BitVec 32} (h : a ++ b = c ++ d) : a = c ∧ b = d := by
  constructor
  · have e := congrArg (BitVec.extractLsb' 32 32) h
    simpa only [BitVec.extractLsb'_append_eq_left] using e
  · have e := congrArg (BitVec.extractLsb' 0 32) h
    simpa only [BitVec.extractLsb'_append_eq_right] using e

theorem finalize_call_ct (hL : L.Ok) (count : BitVec 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (FinArgs L count))
      (.call Spec.Sha512.finalizeApi.name Impl.Sha512.X86.Stream.finalize)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL Proof.Sha512.X86.Stream.Finalize.finalize_verified.1
    Proof.Sha512.X86.Stream.Finalize.finalize_verified.2.1 Whole.finalize_nosp (by rw [Whole.finalize_stack])
  · intro g m t hc hs
    exact finalize_ready hc hL hs
  · intro a b ar aw br bw h
    refine ⟨congrArg (· - 4) (two_esp h), ?_⟩
    intro j hj
    have H := hashSpace hL
    rw [arg_withRegions, arg_withRegions, Whole.call_arg h.1.esp H.below H.frameFit (by omega),
      Whole.call_arg h.2.1.esp H.below H.frameFit (by omega)]
    obtain ⟨a0, a3, a4, ac⟩ := h.2.2.1
    obtain ⟨b0, b3, b4, bc⟩ := h.2.2.2
    have pair := append_pair_eq (ac.trans bc.symm)
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · exact a0.trans b0.symm
    · exact pair.2
    · exact pair.1
    · exact a3.trans b3.symm
    · exact a4.trans b4.symm

theorem finalize_args_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block finalizeArgs)
      (Two L g₁ g₂ m₁ m₂ (FinArgs L (BitVec.ofNat 64 (L.len.toNat + 64)))) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL ha) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩
  · intro s hc _
    exact WP.mono (finalizeArgs_ok hc hL hb) fun _ ⟨hu, _, hs⟩ => ⟨hu, hs⟩

end VG.Proof.Ed25519.X86.VerifyMessage
