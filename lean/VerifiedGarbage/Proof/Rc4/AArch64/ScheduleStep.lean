import VerifiedGarbage.Proof.Rc4.AArch64.Identity
import VerifiedGarbage.Proof.Rc4.Schedule

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4 RegUpd

theorem byte_add3 (a b c : Byte) :
    (a.setWidth 32 + b.setWidth 32 + c.setWidth 32).setWidth 64 &&& 255#64 =
      (a + b + c).setWidth 64 := by
  rw [mask64]
  have h : ((a.setWidth 32 + b.setWidth 32 + c.setWidth 32).setWidth 64).setWidth 8 =
      a + b + c := by bv_omega
  rw [h]

theorem schedule_before (s : State) (i j : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (hj : s.gpr .x13 = j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x17 + s.gpr .x3) 1) :
    WP isa (.block scheduleBefore) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x3 = s.gpr .x3 ∧
      t.gpr .x17 = s.gpr .x17 ∧ t.gpr .x9 = 255#64 ∧ t.gpr .x12 = i.setWidth 64 ∧
      t.gpr .x13 = (j + s.mem (s.gpr .x0 + BitVec.ofNat 64 i.toNat) +
        s.mem (s.gpr .x17 + s.gpr .x3)).setWidth 64 ∧ t.gpr .x4 = t.gpr .x13 ∧
      t.gpr .x14 = (s.mem (s.gpr .x0 + BitVec.ofNat 64 i.toNat)).setWidth 64 := by
  have hr := byte_region _ _ i hp
  have hc (x : Byte) : (x.setWidth 64).setWidth 32 = x.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have hc32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have hc' (x : Byte) : (x.setWidth 32).setWidth 64 = x.setWidth 64 :=
    BitVec.setWidth_setWidth (by decide)
  have haddr : i.setWidth 64 = BitVec.ofNat 64 i.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold scheduleBefore
  rrun [hi, hj, hm, haddr, hr, hk, read_byte, hc, hc32, hc', byte_add3]

/-- Reset the public key offset at the public key length. -/
theorem key_reset (s : State)
    (h4 : s.gpr .x4 = s.gpr .x3 - s.gpr .x1) :
    WP isa (.ite (.zero .x .x4) (.block [.movz .x .x3 0 0]) (.block [])) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x9 = s.gpr .x9 ∧
      t.gpr .x12 = s.gpr .x12 ∧ t.gpr .x13 = s.gpr .x13 ∧ t.gpr .x17 = s.gpr .x17 ∧
      t.gpr .x3 = if s.gpr .x3 = s.gpr .x1 then 0#64 else s.gpr .x3 := by
  have heq : s.gpr .x3 - s.gpr .x1 = 0#64 ↔ s.gpr .x3 = s.gpr .x1 := by bv_omega
  refine WP.ite (decide (s.gpr .x3 = s.gpr .x1)) ?_ (fun h => ?_) (fun h => ?_)
  · simp only [eval, State.read, BitVec.setWidth_eq, h4, BitVec.ofNat_eq_ofNat]
    apply congrArg some
    by_cases hh : s.gpr .x3 = s.gpr .x1
    · rw [hh, BitVec.sub_self]
      simp only [beq_self_eq_true, decide_true]
    · rw [beq_eq_false_iff_ne.mpr (fun h => hh (heq.mp h)), decide_eq_false hh]
  · have hh : s.gpr .x3 = s.gpr .x1 := of_decide_eq_true h
    rrun [hh]
  · have hh : ¬ s.gpr .x3 = s.gpr .x1 := of_decide_eq_false h
    rrun [hh]

theorem schedule_after (s : State) (i b : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (hb : s.gpr .x6 = b.setWidth 64)
    (hp : InRegions s.wr (s.gpr .x0) 256) :
    WP isa scheduleAfter s fun t =>
      t.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x9 = s.gpr .x9 ∧
      t.gpr .x13 = s.gpr .x13 ∧ t.gpr .x17 = s.gpr .x17 ∧
      t.gpr .x3 = (if s.gpr .x3 + 1#64 = s.gpr .x1 then 0#64 else s.gpr .x3 + 1#64) ∧
      t.gpr .x12 = i.setWidth 64 + 1#64 ∧ t.gpr .x11 = i.setWidth 64 + 1#64 - 256#64 := by
  have hw := byte_region _ _ i hp
  have hc (x : Byte) : (x.setWidth 64).setWidth 32 = x.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have hc8 (x : Byte) : (x.setWidth 32).setWidth 8 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have haddr : i.setWidth 64 = BitVec.ofNat 64 i.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have hpre : WP isa (.block [.add .x .x7 .x0 .x12, .strb .x6 .x7 0,
      .addImm .x .x3 .x3 1, .sub .x .x4 .x3 .x1]) s fun t =>
      t.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x0 = s.gpr .x0 ∧
      t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x9 = s.gpr .x9 ∧ t.gpr .x12 = i.setWidth 64 ∧
      t.gpr .x13 = s.gpr .x13 ∧ t.gpr .x17 = s.gpr .x17 ∧
      t.gpr .x3 = s.gpr .x3 + 1#64 ∧ t.gpr .x4 = t.gpr .x3 - t.gpr .x1 := by
    rrun [State.store, hi, hb, haddr, hc, hc8, hw]
  unfold scheduleAfter
  refine WP.seq (WP.mono hpre fun t ht => ?_)
  obtain ⟨htm, htr, htw, ht0, ht1, ht9, ht12, ht13, ht17, ht3, ht4⟩ := ht
  refine WP.seq (WP.mono (key_reset t ht4) fun u hu => ?_)
  obtain ⟨hum, hur, huw, hu0, hu1, hu9, hu12, hu13, hu17, hu3⟩ := hu
  rrun [hum, hur, huw, hu0, hu1, hu9, hu12, hu13, hu17, hu3,
    htm, htr, htw, ht0, ht1, ht9, ht12, ht13, ht17, ht3]

/-- One concrete key-scheduling round, preserving the original swap operands. -/
theorem schedule_step (s : State) (i j : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (hj : s.gpr .x13 = j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hp : InRegions s.wr (s.gpr .x0) 256)
    (hk : InRegions (s.rd ++ s.wr) (s.gpr .x17 + s.gpr .x3) 1) :
    let a := s.mem (s.gpr .x0 + BitVec.ofNat 64 i.toNat)
    let jj := j + a + s.mem (s.gpr .x17 + s.gpr .x3)
    let b := s.mem (s.gpr .x0 + BitVec.ofNat 64 jj.toNat)
    WP isa scheduleStep s fun t =>
      t.mem = (s.mem.write (s.gpr .x0 + BitVec.ofNat 64 jj.toNat) 1 a).write
        (s.gpr .x0 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧
      t.gpr .x9 = 255#64 ∧ t.gpr .x17 = s.gpr .x17 ∧
      t.gpr .x3 = (if s.gpr .x3 + 1#64 = s.gpr .x1 then 0#64 else s.gpr .x3 + 1#64) ∧
      t.gpr .x12 = i.setWidth 64 + 1#64 ∧ t.gpr .x13 = jj.setWidth 64 ∧
      t.gpr .x11 = i.setWidth 64 + 1#64 - 256#64 := by
  dsimp only
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256 := by
    obtain ⟨region, hregion, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hregion, hc⟩
  unfold scheduleStep
  refine WP.seq (WP.mono (schedule_before s i j hi hj hm hr hk) fun t ht => ?_)
  obtain ⟨htm, htr, htw, ht0, ht1, ht3, ht17, ht9, ht12, ht13, ht4, ht14⟩ := ht
  have htp : InRegions t.wr (t.gpr .x0) 256 := by rw [htw, ht0]; exact hp
  refine WP.seq (WP.mono (replace_ok t _ _ (ht4.trans ht13) ht14 htp) fun u hu => ?_)
  obtain ⟨hkeep, hum, hu6, hu9⟩ := hu
  have hu0 := (hkeep.1 .x0 (by decide)).trans ht0
  have hu1 := (hkeep.1 .x1 (by decide)).trans ht1
  have hu3 := (hkeep.1 .x3 (by decide)).trans ht3
  have hu17 := (hkeep.1 .x17 (by decide)).trans ht17
  have hu12 := (hkeep.1 .x12 (by decide)).trans ht12
  have hu13 := (hkeep.1 .x13 (by decide)).trans ht13
  have hur := hkeep.2.1.trans htr
  have huw := hkeep.2.2.trans htw
  rw [htm, ht0] at hum hu6
  have hup : InRegions u.wr (u.gpr .x0) 256 := by rw [huw, hu0]; exact hp
  refine WP.mono (schedule_after u i _ hu12 hu6 hup) fun v hv => ?_
  obtain ⟨hvm, hvr, hvw, hv0, hv1, hv9, hv13, hv17, hv3, hv12, hv11⟩ := hv
  refine ⟨?_, hvr.trans hur, hvw.trans huw, hv0.trans hu0, hv1.trans hu1,
    hv9.trans hu9, hv17.trans hu17, ?_, hv12, hv13.trans hu13, hv11⟩
  · simpa only [hum, hu0] using hvm
  · simpa only [hu3, hu1] using hv3

end VG.Proof.Rc4.AArch64
