import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.HashUpdate

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem input_geometry (hL : L.Ok) {p n : BitVec 32} {R : Region}
    (hr : R ∈ L.inputs) (hw : Whole.Within ⟨p.setWidth 64, n.toNat⟩ R)
    (hf : p.toNat + n.toNat ≤ 2 ^ 32) : Input L p n := by
  refine ⟨.inr ⟨R, List.mem_append_left _ hr, hw⟩, (hL.sc _ hr).sub_left hw.sub,
    ((hL.ks _ hr).sub_left (Whole.below_sub_stack hL.below (by simp))).sub_right hw.sub, ?_, hf⟩
  exact ((hL.ks _ hr).sub_left (fun p hp => Whole.frame_sub L.E p
    ((argsWithin L (n := 24) (by simp)).sub p hp))).symm.sub_left hw.sub

theorem input_pk (hL : L.Ok) : Input L L.pk 32 :=
  input_geometry hL (R := L.PK) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 32; decide⟩ hL.np

theorem input_sig (hL : L.Ok) : Input L L.sig 32 :=
  input_geometry hL (R := L.SIG) (by simp [Lay.inputs]) ⟨0, by simp, by change 0 + 32 ≤ 64; decide⟩
    (by change L.sig.toNat + 32 ≤ 2 ^ 32; have := hL.ns; omega)

theorem input_msg (hL : L.Ok) : Input L L.msg L.len :=
  input_geometry hL (R := L.MSG) (by simp [Lay.inputs]) ⟨0, by simp, by simp⟩ hL.nm

theorem prefix_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {source count : Nat} (hs : source < 5) {prev : List Byte}
    (hlen : prev.length = count) (hcount : count < 2 ^ 32)
    (hi : Input L (L.value source) 32)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update (Impl.Ed25519.X86.VerifyMessage.prefixArgs source count)) s
      fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem ((L.value source).setWidth 64) 32) := by
  apply update_step hc hL ha (vs := [.caller 4 0, .const count, .const 0,
    .caller source 0, .const 32, .caller 4 192]) (by simp)
    (by simp [Whole.valid, hs]) (c := BitVec.ofNat 32 count) (p := L.value source) (n := 32)
    ?_ hi (by simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount] using hlen.symm) hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 4) (by simp) (by simp)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

theorem message_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    {prev : List Byte} (hlen : prev.length = 64)
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 s.mem (L.scr.setWidth 64) prev) :
    WP isa (Impl.Ed25519.X86.VerifyMessage.update Impl.Ed25519.X86.VerifyMessage.messageArgs) s
      fun t => Ctx L g m₀ t ∧ Frame (hashWrites L) s.mem t.mem ∧
      Spec.Sha512.Repr Spec.Sha512.H0_512 t.mem (L.scr.setWidth 64)
        (prev ++ Spec.Ed25519.bytesAt s.mem (L.msg.setWidth 64) L.len.toNat) := by
  apply update_step hc hL ha (vs := [.caller 4 0, .const 64, .const 0,
    .caller 1 0, .caller 2 0, .caller 4 192]) (by simp)
    (by simp [Whole.valid]) (c := 64) (p := L.msg) (n := L.len)
    ?_ (input_msg hL) hlen.symm hr
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ht.slot hL (j := 0) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 1) (by simp) (by simp)
  · exact ht.slot hL (j := 2) (by simp) (by simp)
  · exact (ht.slot hL (j := 3) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact (ht.slot hL (j := 4) (by simp) (by simp)).trans (BitVec.add_zero _)
  · exact ht.slot hL (j := 5) (by simp) (by simp)

end VG.Proof.Ed25519.X86.VerifyMessage
