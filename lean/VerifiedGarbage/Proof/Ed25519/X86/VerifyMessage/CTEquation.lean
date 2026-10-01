import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.CTScalars

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.VerifyMessage

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

def equationValues : List Value := [.caller 0 0, .caller 3 0, .frame 128, .caller 4 0]
def EqState (L : Lay) (ch : List Byte) (s : State) : Prop :=
  OutArgs L equationValues s ∧ Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = ch

theorem eq_args (hL : L.Ok) {s : State} (hs : OutArgs L equationValues s) : EqArgs L s :=
  ⟨(hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _),
    (hs.slot hL (j := 1) (by decide) (by decide)).trans (BitVec.add_zero _),
    hs.slot hL (j := 2) (by decide) (by decide),
    (hs.slot hL (j := 3) (by decide) (by decide)).trans (BitVec.add_zero _)⟩

theorem ce_input {g : Reg → BitVec 32} {m : Mem} {s : State}
    (hc : Ctx L g m s) (hL : L.Ok) {r : Region} (hr : r ∈ L.inputs) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt s.callEntry.mem r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  have e := Whole.callEntry_bytes (t := s) (r := r) (by
    rw [hc.esp]
    exact ((hL.ks _ hr).sub_left (Whole.below_sub_stack hL.below (by decide))).symm) hn
  exact e.trans (hc.input_bytes hL hr hn)

theorem ce_challenge {g : Reg → BitVec 32} {m : Mem} {s : State}
    (hc : Ctx L g m s) (hL : L.Ok) {ch : List Byte}
    (he : Spec.Ed25519.bytesAt s.mem (L.E.setWidth 64 + 128) 64 = ch) :
    Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 = ch := by
  have e := Whole.callEntry_bytes (t := s) (r := challenge L) (by
    rw [hc.esp]
    exact (Whole.frame_below hL.below (hashSpace hL).frameFit
      (by decide : 128 < 256) (by decide : 128 + 64 ≤ 256)).symm) (by change 64 ≤ 2 ^ 64; decide)
  have ea : (L.E + 128).setWidth 64 = L.E.setWidth 64 + 128 :=
    Whole.frame_addr (hashSpace hL).frameFit (by decide : 128 < 256)
  change Spec.Ed25519.bytesAt s.callEntry.mem ((L.E + 128).setWidth 64) 64 =
    Spec.Ed25519.bytesAt s.mem ((L.E + 128).setWidth 64) 64 at e
  rw [ea] at e ⊢
  exact e.trans he

theorem equation_call_ct (hL : L.Ok) (ch : List Byte)
    (hp : Spec.Ed25519.bytesAt m₁ (L.pk.setWidth 64) 32 = Spec.Ed25519.bytesAt m₂ (L.pk.setWidth 64) 32)
    (hs : Spec.Ed25519.bytesAt m₁ (L.sig.setWidth 64) 64 = Spec.Ed25519.bytesAt m₂ (L.sig.setWidth 64) 64) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (EqState L ch))
      (.call "vg_ed25519_verify_equation" Impl.Ed25519.X86.verifyEquation)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL equation_correct_result verify_ct equation_nosp (by rw [equation_stack]; decide)
  · intro g m t hc hh
    exact equation_ready hc hL (eq_args hL hh.1)
  · intro a b ar aw br bw h
    have hargs : Two L g₁ g₂ m₁ m₂ (OutArgs L equationValues) a b := ⟨h.1, h.2.1, h.2.2.1.1, h.2.2.2.1⟩
    have hj {j : Nat} (hh : j < 4) := call_args_eq hL (by decide) hargs hh
    have H := hashSpace hL
    have ea := eq_args hL h.2.2.1.1
    have eb := eq_args hL h.2.2.2.1
    have a0 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 0 < 64)).trans ea.1
    have a1 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 1 < 64)).trans ea.2.1
    have a2 := (Whole.call_arg h.1.esp H.below H.frameFit (by decide : 2 < 64)).trans ea.2.2.1
    have b0 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 0 < 64)).trans eb.1
    have b1 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 1 < 64)).trans eb.2.1
    have b2 := (Whole.call_arg h.2.1.esp H.below H.frameFit (by decide : 2 < 64)).trans eb.2.2.1
    refine ⟨congrArg (· - 4) (two_esp h), hj (by decide), hj (by decide), hj (by decide), hj (by decide), ?_, ?_, ?_⟩
    · simp only [arg_withRegions, State.withRegions_mem, a0, b0]
      exact (ce_input h.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)).trans
        (hp.trans (ce_input h.2.1 hL (r := L.PK) (by simp [Lay.inputs]) (by change 32 ≤ 2 ^ 64; decide)).symm)
    · simp only [arg_withRegions, State.withRegions_mem, a1, b1]
      exact (ce_input h.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)).trans
        (hs.trans (ce_input h.2.1 hL (r := L.SIG) (by simp [Lay.inputs]) (by change 64 ≤ 2 ^ 64; decide)).symm)
    · simp only [arg_withRegions, State.withRegions_mem, a2, b2]
      exact (ce_challenge h.1 hL h.2.2.1.2).trans (ce_challenge h.2.1 hL h.2.2.2.2).symm

theorem equation_setup_ct (hL : L.Ok) (ha : Arguments L m₁) (hb : Arguments L m₂) (ch : List Byte) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun t => Spec.Ed25519.bytesAt t.mem (L.E.setWidth 64 + 128) 64 = ch)
      (.block equationArgs) (Two L g₁ g₂ m₁ m₂ (EqState L ch)) := by
  have ct := setup_ct (g₁ := g₁) (g₂ := g₂) hL ha hb equationValues
    (by decide) (by simp [equationValues, Whole.valid]) (by taint_decide)
  refine two_wp (ct.mono (fun _ _ h => ⟨h.1, h.2.1, trivial, trivial⟩) (fun _ _ _ => trivial)) ?_ ?_
  · intro t hc hd
    refine WP.mono (args_ok hc hL ha (vs := equationValues) (by decide)
      (by simp [equationValues, Whole.valid])) fun u ⟨hu, hf, hs⟩ => ⟨hu, hs, ?_⟩
    exact (setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)).trans hd
  · intro t hc hd
    refine WP.mono (args_ok hc hL hb (vs := equationValues) (by decide)
      (by simp [equationValues, Whole.valid])) fun u ⟨hu, hf, hs⟩ => ⟨hu, hs, ?_⟩
    exact (setup_bytes hf (by decide : 24 ≤ 128) (by decide : 128 + 64 ≤ 256)).trans hd

end VG.Proof.Ed25519.X86.VerifyMessage
