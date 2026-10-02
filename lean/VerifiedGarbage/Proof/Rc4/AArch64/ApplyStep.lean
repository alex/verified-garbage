import VerifiedGarbage.Proof.Rc4.AArch64.Replace

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 RegUpd VG.Spec.Rc4 VG.Proof.Rc4

theorem mask64 (x : BitVec 64) : x &&& 255#64 = (x.setWidth 8).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hmask : (255#64 : BitVec 64).getLsbD k = decide (k < 8) := by
    change Nat.testBit 255 k = decide (k < 8)
    exact Nat.testBit_two_pow_sub_one 8 k
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hmask, hk,
    decide_true, Bool.true_and]
  rw [Bool.and_comm]

theorem byte_inc (i : Byte) :
    (i.setWidth 64 + 1#64) &&& 255#64 = (i + 1#8).setWidth 64 := by
  rw [mask64]
  have h : (i.setWidth 64 + 1#64).setWidth 8 = i + 1#8 := by bv_omega
  rw [h]

theorem byte_add (a b : Byte) :
    (a.setWidth 32 + b.setWidth 32).setWidth 64 &&& 255#64 = (a + b).setWidth 64 := by
  rw [mask64]
  have h : ((a.setWidth 32 + b.setWidth 32).setWidth 64).setWidth 8 = a + b := by bv_omega
  rw [h]

theorem read_byte (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p : BitVec 8) = m p
  exact BitVec.zero_width_append _ _

theorem byte_region (rs : List Region) (p : Addr) (idx : Byte)
    (hp : InRegions rs p 256) : InRegions rs (p + BitVec.ofNat 64 idx.toNat) 1 := by
  obtain ⟨region, hregion, hcontains⟩ := hp
  refine ⟨region, hregion, ?_⟩
  unfold Region.Contains at hcontains ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega)]
  have hmod := Nat.mod_le ((p - region.base).toNat + idx.toNat) (2 ^ 64)
  have hb := idx.isLt
  omega

theorem apply_before (s : State) (i j : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (hj : s.gpr .x13 = j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256) :
    WP isa (.block applyBefore) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x9 = 255#64 ∧ t.gpr .x12 = (i + 1#8).setWidth 64 ∧
      t.gpr .x13 = (j + s.mem (s.gpr .x0 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 ∧
      t.gpr .x4 = t.gpr .x13 ∧
      t.gpr .x14 = (s.mem (s.gpr .x0 + BitVec.ofNat 64 (i + 1#8).toNat)).setWidth 64 := by
  have hr := byte_region _ _ (i + 1#8) hp
  have hc (x : Byte) : (x.setWidth 64).setWidth 32 = x.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have hc' (x : Byte) : (x.setWidth 32).setWidth 64 = x.setWidth 64 :=
    BitVec.setWidth_setWidth (by decide)
  have ha : (i + 1#8).setWidth 64 = BitVec.ofNat 64 (i + 1#8).toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold applyBefore
  rrun [hi, hj, hm, byte_inc, ha, hr, read_byte, hc, hc', byte_add]

theorem apply_middle (s : State) (i a b : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (ha : s.gpr .x14 = a.setWidth 64)
    (hb : s.gpr .x6 = b.setWidth 64) (hm : s.gpr .x9 = 255#64)
    (hp : InRegions s.wr (s.gpr .x0) 256) :
    WP isa (.block applyMiddle) s fun t =>
      t.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 i.toNat) 1 b ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x9 = 255#64 ∧ t.gpr .x12 = s.gpr .x12 ∧ t.gpr .x13 = s.gpr .x13 ∧
      t.gpr .x4 = (a + b).setWidth 64 := by
  have hw := byte_region _ _ i hp
  have hc (x : Byte) : (x.setWidth 64).setWidth 32 = x.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have hc8 (x : Byte) : (x.setWidth 64).setWidth 8 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have hc832 (x : Byte) : (x.setWidth 32).setWidth 8 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have haddr : i.setWidth 64 = BitVec.ofNat 64 i.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold applyMiddle
  rrun [State.store, hi, ha, hb, hm, hc, hc8, hc832, haddr, hw, byte_add]

theorem byte_xor (a b : Byte) :
    (a.setWidth 32 ^^^ b.setWidth 32).setWidth 8 = a ^^^ b := by
  rw [BitVec.setWidth_xor]
  congr 1 <;> exact (BitVec.setWidth_setWidth_of_le _ (by decide)).trans (BitVec.setWidth_eq _)

theorem apply_after (s : State) (k : Byte) (hk : s.gpr .x6 = k.setWidth 64)
    (hp : InRegions s.wr (s.gpr .x1) 1) :
    WP isa (.block applyAfter) s fun t =>
      t.mem = s.mem.write (s.gpr .x1) 1 (s.mem (s.gpr .x1) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x0 = s.gpr .x0 ∧
      t.gpr .x1 = s.gpr .x1 + 1#64 ∧ t.gpr .x2 = s.gpr .x2 - 1#64 ∧
      t.gpr .x12 = s.gpr .x12 ∧ t.gpr .x13 = s.gpr .x13 ∧ t.gpr .x9 = s.gpr .x9 := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x1) 1 := by
    obtain ⟨region, hregion, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hregion, hc⟩
  have hc (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have hc' (x : Byte) : (x.setWidth 64).setWidth 32 = x.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have hc8 (x : BitVec 32) : (x.setWidth 64).setWidth 8 = x.setWidth 8 :=
    BitVec.setWidth_setWidth (by decide)
  unfold applyAfter
  rrun [State.store, hk, hp, hr, read_byte, hc, hc', hc8, byte_xor]

/-- One iteration, with the writes expressed against the original memory.
Both swap operands are read before either write, including for a self-swap. -/
theorem apply_step (s : State) (i j : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (hj : s.gpr .x13 = j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hp : InRegions s.wr (s.gpr .x0) 256)
    (hd : InRegions s.wr (s.gpr .x1) 1) :
    let ii := i + 1#8
    let a := s.mem (s.gpr .x0 + BitVec.ofNat 64 ii.toNat)
    let jj := j + a
    let b := s.mem (s.gpr .x0 + BitVec.ofNat 64 jj.toNat)
    let swapped := (s.mem.write (s.gpr .x0 + BitVec.ofNat 64 jj.toNat) 1 a).write
      (s.gpr .x0 + BitVec.ofNat 64 ii.toNat) 1 b
    let k := swapped (s.gpr .x0 + BitVec.ofNat 64 (a + b).toNat)
    WP isa applyStep s fun t =>
      t.mem = swapped.write (s.gpr .x1) 1 (swapped (s.gpr .x1) ^^^ k) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x0 = s.gpr .x0 ∧
      t.gpr .x1 = s.gpr .x1 + 1#64 ∧ t.gpr .x2 = s.gpr .x2 - 1#64 ∧
      t.gpr .x9 = 255#64 ∧ t.gpr .x12 = ii.setWidth 64 ∧ t.gpr .x13 = jj.setWidth 64 := by
  dsimp only
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256 := by
    obtain ⟨region, hregion, hc⟩ := hp
    exact ⟨region, List.mem_append_right _ hregion, hc⟩
  unfold applyStep
  refine WP.seq (WP.mono (apply_before s i j hi hj hm hr) fun t ht => ?_)
  obtain ⟨htm, htr, htw, ht0, ht1, ht2, ht9, ht12, ht13, ht4, ht14⟩ := ht
  have htp : InRegions t.wr (t.gpr .x0) 256 := by rw [htw, ht0]; exact hp
  refine WP.seq (WP.mono (replace_ok t _ _ (ht4.trans ht13) ht14 htp) fun u hu => ?_)
  obtain ⟨hkeep, hum, hu6, hu9⟩ := hu
  have hu0 := (hkeep.1 .x0 (by decide)).trans ht0
  have hu1 := (hkeep.1 .x1 (by decide)).trans ht1
  have hu2 := (hkeep.1 .x2 (by decide)).trans ht2
  have hu12 := (hkeep.1 .x12 (by decide)).trans ht12
  have hu13 := (hkeep.1 .x13 (by decide)).trans ht13
  have hu14 := (hkeep.1 .x14 (by decide)).trans ht14
  have hur := hkeep.2.1.trans htr
  have huw := hkeep.2.2.trans htw
  rw [htm, ht0] at hum hu6
  have hup : InRegions u.wr (u.gpr .x0) 256 := by rw [huw, hu0]; exact hp
  refine WP.seq (WP.mono (apply_middle u _ _ _ hu12 hu14 hu6 hu9 hup) fun v hv => ?_)
  obtain ⟨hvm, hvr, hvw, hv0, hv1, hv2, hv9, hv12, hv13, hv4⟩ := hv
  have hvp : InRegions (v.rd ++ v.wr) (v.gpr .x0) 256 := by
    rw [hvr, hvw, hur, huw, hv0, hu0]; exact hr
  refine WP.seq (WP.mono (lookup_ok v _ hv4 hvp) fun w hw => ?_)
  obtain ⟨hwkeep, hwm, hw6, hw9⟩ := hw
  have hw0 := (hwkeep.1 .x0 (by decide)).trans (hv0.trans hu0)
  have hw1 := (hwkeep.1 .x1 (by decide)).trans (hv1.trans hu1)
  have hw2 := (hwkeep.1 .x2 (by decide)).trans (hv2.trans hu2)
  have hw12 := (hwkeep.1 .x12 (by decide)).trans (hv12.trans hu12)
  have hw13 := (hwkeep.1 .x13 (by decide)).trans (hv13.trans hu13)
  have hwr := hwkeep.2.1.trans (hvr.trans hur)
  have hww := hwkeep.2.2.trans (hvw.trans huw)
  have hwd : InRegions w.wr (w.gpr .x1) 1 := by rw [hww, hw1]; exact hd
  refine WP.mono (apply_after w _ hw6 hwd) fun z hz => ?_
  obtain ⟨hzm, hzr, hzw, hz0, hz1, hz2, hz12, hz13, hz9⟩ := hz
  refine ⟨?_, hzr.trans hwr, hzw.trans hww, hz0.trans hw0, ?_, ?_, ?_,
    hz12.trans hw12, hz13.trans hw13⟩
  · simpa only [hwm, hvm, hum, hu0, hv0, hw1] using hzm
  · rw [hz1, hw1]
  · rw [hz2, hw2]
  · rw [hz9]
    exact hw9

/-- The concrete stream iteration realizes the abstract PRGA transition. -/
theorem apply_step_table (s : State) (i j : Byte)
    (hi : s.gpr .x12 = i.setWidth 64) (hj : s.gpr .x13 = j.setWidth 64)
    (hm : s.gpr .x9 = 255#64) (hp : InRegions s.wr (s.gpr .x0) 256)
    (hd : InRegions s.wr (s.gpr .x1) 1)
    (hs : Mem.Sep (s.gpr .x0) 256 (s.gpr .x1) 1) :
    let next := step { table := (contextAt s.mem (s.gpr .x0)).table, i, j }
    WP isa applyStep s fun t =>
      (contextAt t.mem (s.gpr .x0)).table = next.1.table ∧
      t.gpr .x12 = next.1.i.setWidth 64 ∧ t.gpr .x13 = next.1.j.setWidth 64 ∧
      t.mem (s.gpr .x1) = s.mem (s.gpr .x1) ^^^ next.2 ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.gpr .x0 = s.gpr .x0 ∧
      t.gpr .x1 = s.gpr .x1 + 1#64 ∧ t.gpr .x2 = s.gpr .x2 - 1#64 ∧
      t.gpr .x9 = 255#64 := by
  dsimp only
  rw [step_eq]
  dsimp only
  simp only [table_get]
  have hone : (1 : Byte) = 1#8 := rfl
  simp only [hone]
  refine WP.mono (apply_step s i j hi hj hm hp hd) fun t ht => ?_
  obtain ⟨hmem, hrd, hwr, h0, h1, h2, h9, h12, h13⟩ := ht
  refine ⟨?_, h12, h13, ?_, hrd, hwr, h0, h1, h2, h9⟩
  · rw [hmem, table_write_sep _ _ _ _ hs, table_swap]
  · rw [hmem, write_byte, ite_eq_left rfl]
    have hne (idx : Byte) : s.gpr .x1 ≠ s.gpr .x0 + BitVec.ofNat 64 idx.toNat := by
      intro he
      have hn := hs (s.gpr .x1) (by rw [he, Mem.sub_ofNat_toNat _ (by omega)]; exact idx.isLt)
      exact hn (by simp [BitVec.sub_self])
    rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]
    have ht := table_swap s.mem (s.gpr .x0) (i + 1#8)
      (j + s.mem (s.gpr .x0 + BitVec.ofNat 64 (i + 1#8).toNat))
    rw [← ht, table_get]

end VG.Proof.Rc4.AArch64
