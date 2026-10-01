import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashUpdate

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole

variable {L : Lay}

theorem update_args {t : State} (hL : L.Ok) (c : Nat) (p n : Value)
    (h : OutArgs L [.caller 5 0, .const c, .const 0, p, n, .caller 5 192] t) :
    UpdateArgs L (BitVec.ofNat 32 c) (value L p) (value L n) t := by
  have h0 := h.slot hL (j := 0) (by simp) (by simp)
  have h1 := h.slot hL (j := 1) (by simp) (by simp)
  have h2 := h.slot hL (j := 2) (by simp) (by simp)
  have h3 := h.slot hL (j := 3) (by simp) (by simp)
  have h4 := h.slot hL (j := 4) (by simp) (by simp)
  have h5 := h.slot hL (j := 5) (by simp) (by simp)
  change Whole.slots L.E t 0 = L.scr + 0#32 at h0
  rw [BitVec.add_zero] at h0
  exact ⟨h0, h1, h2, h3, h4, h5⟩

theorem Input.external {p n : BitVec 32}
    (hc : ∃ R ∈ L.inputs ++ L.outputs, Whole.Within ⟨p.setWidth 64, n.toNat⟩ R)
    (hs : Region.Disjoint ⟨p.setWidth 64, n.toNat⟩ L.SCR)
    (hk : L.STK.Disjoint ⟨p.setWidth 64, n.toNat⟩)
    (hL : L.Ok) (hf : p.toNat + n.toNat ≤ 2 ^ 32) : Input L p n :=
  ⟨.inr hc, hs, hk.sub_left (Whole.below_sub_stack hL.below (by decide)),
    (hk.sub_left (fun a ha => Whole.frame_sub L.E a (Region.sub_prefix (by decide : 24 ≤ 256) a ha))).symm, hf⟩

theorem seed_input (hL : L.Ok) : Input L L.seed 32 :=
  Input.external ⟨L.SEED, by simp [Lay.inputs], 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.ns

theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  Input.external ⟨L.PK, by simp [Lay.inputs], 0, by simp, by change 0 + 32 ≤ 32; decide⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.np

theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  Input.external ⟨L.MSG, by simp [Lay.inputs], 0, by simp, by simp⟩
    (hL.sc _ (by simp [Lay.inputs])) (hL.ks _ (by simp [Lay.inputs])) hL hL.nm

theorem point_input (hL : L.Ok) : Input L L.out 32 :=
  Input.external ⟨L.OUT, by simp [Lay.outputs], 0, by simp, by change 0 + 32 ≤ 64; decide⟩
    (hL.oc.sub_left (Region.sub_prefix (by decide)))
    (hL.ko.sub_right (Region.sub_prefix (by decide))) hL (by change L.out.toNat + 32 ≤ 2 ^ 32; have := hL.no; omega)

theorem prefix_input (hL : L.Ok) : Input L (L.E + 64) 32 := by
  have ea : (L.E + 64).setWidth 64 = L.E.setWidth 64 + 64 :=
    addr_eq (x := L.E) (k := 64) (by have := hL.top; omega)
  have hin : Whole.Within ⟨(L.E + 64).setWidth 64, (32 : BitVec 32).toNat⟩ L.FR :=
    ⟨64, ea, by change 64 + 32 ≤ 256; decide⟩
  refine ⟨.inl hin, hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (hin.sub p hp)), ?_, ?_, ?_⟩
  · change Region.Disjoint ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩ _
    rw [Taint.sub_setWidth hL.below, ea]
    exact (Offset.disjoint_below _ (n := 24) (d := 64) (k := 32) (by decide)).symm
  · rw [ea]
    exact Offset.disjoint_base _ (d := 64) (n := 32) (k := 24) (by decide) (by decide)
  · rw [BitVec.toNat_add, show (64 : BitVec 32).toNat = 64 from rfl,
      Nat.mod_eq_of_lt (by have := hL.top; omega)]
    have := hL.top; change L.E.toNat + 64 + 32 ≤ 2 ^ 32; omega

end VG.Proof.Ed25519.X86.SignCached
