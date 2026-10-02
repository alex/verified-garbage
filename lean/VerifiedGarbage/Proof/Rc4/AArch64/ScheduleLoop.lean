import VerifiedGarbage.Proof.Rc4.AArch64.ScheduleStep

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

def keyAt (s : State) : List Byte := bytesAt s.mem (s.gpr .x17) (s.gpr .x1).toNat

structure ScheduleInv (s₀ : State) (r : Nat) (s : State) : Prop where
  frame : TableFrame (s₀.gpr .x0) s₀.mem s.mem
  table : (contextAt s.mem (s₀.gpr .x0)).table = (schedulePrefix (keyAt s₀) r).1
  j : s.gpr .x13 = (schedulePrefix (keyAt s₀) r).2.setWidth 64
  i : s.gpr .x12 = BitVec.ofNat 64 r
  off : s.gpr .x3 = BitVec.ofNat 64 (r % (s₀.gpr .x1).toNat)
  p : s.gpr .x0 = s₀.gpr .x0
  len : s.gpr .x1 = s₀.gpr .x1
  key : s.gpr .x17 = s₀.gpr .x17
  mask : s.gpr .x9 = 255#64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem key_next_offset (r len : Nat) (hl : 0 < len) (hlen : len ≤ 256) :
    (if BitVec.ofNat 64 (r % len) + 1#64 = BitVec.ofNat 64 len then 0#64
      else BitVec.ofNat 64 (r % len) + 1#64) = BitVec.ofNat 64 ((r + 1) % len) := by
  have hb := Nat.mod_lt r hl
  have ha : (r + 1) % len = (r % len + 1) % len := by
    simp only [Nat.add_mod, Nat.mod_mod]
  rw [ha]
  by_cases h : r % len + 1 = len
  · have he : BitVec.ofNat 64 (r % len) + 1#64 = BitVec.ofNat 64 len := by bv_omega
    rw [ite_eq_left he, h, Nat.mod_self]
  · have he : BitVec.ofNat 64 (r % len) + 1#64 ≠ BitVec.ofNat 64 len := by bv_omega
    rw [ite_eq_right he, Nat.mod_eq_of_lt (show r % len + 1 < len by omega)]
    bv_omega

theorem schedule_inv_step (s₀ s : State) (r : Nat) (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .x1).toNat ∧ (s₀.gpr .x1).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .x0) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x17) (s₀.gpr .x1).toNat)
    (hs : Mem.Sep (s₀.gpr .x17) (s₀.gpr .x1).toNat (s₀.gpr .x0) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa scheduleStep s fun t => ScheduleInv s₀ (r + 1) t ∧
      t.gpr .x11 = BitVec.ofNat 64 (r + 1) - 256#64 := by
  let key := keyAt s₀
  let st := schedulePrefix key r
  have hi : s.gpr .x12 = (BitVec.ofNat 8 r).setWidth 64 := by
    rw [h.i]
    bv_omega
  have hrt : (BitVec.ofNat 8 r).toNat = r := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
  have hpoint : InRegions s.wr (s.gpr .x0) 256 := by rw [h.wr, h.p]; exact hp
  have hmod := Nat.mod_lt r (show 0 < (s₀.gpr .x1).toNat by omega)
  have hkeypoint : InRegions (s.rd ++ s.wr) (s.gpr .x17 + s.gpr .x3) 1 := by
    rw [h.rd, h.wr, h.key, h.off]
    exact region_offset _ _ _ _ _ (by omega) (by omega) hk
  have hkeybyte : s.mem (s.gpr .x17 + s.gpr .x3) =
      key.getD (r % key.length) 0 := by
    rw [h.key, h.off]
    have hsep := hs (s₀.gpr .x17 + BitVec.ofNat 64 (r % (s₀.gpr .x1).toNat))
      (by rw [Mem.sub_ofNat_toNat _ (by omega)]; exact hmod)
    rw [h.frame _ hsep]
    dsimp only [key, keyAt]
    rw [bytes_length, bytes_get _ _ _ _ hmod]
  have htablebyte : s.mem (s.gpr .x0 + BitVec.ofNat 64 r) = st.1.getD r 0 := by
    rw [h.p]
    have hg := table_get s.mem (s₀.gpr .x0) (BitVec.ofNat 8 r)
    rw [hrt, h.table] at hg
    exact hg.symm
  have hj : s.gpr .x13 = st.2.setWidth 64 := h.j
  refine WP.mono (schedule_step s _ _ hi hj h.mask hpoint hkeypoint) fun t ht => ?_
  obtain ⟨htm, htr, htw, ht0, ht1, ht9, ht17, ht3, ht12, ht13, ht11⟩ := ht
  have hnext := schedule_succ key r
  dsimp only [scheduleRound] at hnext
  have hcast : (BitVec.ofNat 8 r).setWidth 64 + 1#64 = BitVec.ofNat 64 (r + 1) := by bv_omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ht0.trans h.p, ht1.trans h.len,
    ht17.trans h.key, ht9, htr.trans h.rd, htw.trans h.wr⟩, ?_⟩
  · rw [htm, h.p]
    exact h.frame.trans (swap_frame _ _ _ _)
  · rw [htm, h.p, table_swap, h.table, hnext, hrt]
    have hb := htablebyte
    rw [h.p] at hb
    rw [hb, hkeybyte]
  · rw [ht13, hrt, htablebyte, hkeybyte, hnext]
  · rw [ht12, hcast]
  · rw [ht3, h.off, h.len]
    have hn : BitVec.ofNat 64 (s₀.gpr .x1).toNat = s₀.gpr .x1 := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    simpa only [hn] using key_next_offset r _ (by omega) hlen.2
  · rw [ht11, hcast]

/-- All 256 scheduling rounds realize the complete specified permutation. -/
theorem schedule_loop (s₀ s : State) (r : Nat) (hr : r < 256)
    (hlen : 1 ≤ (s₀.gpr .x1).toNat ∧ (s₀.gpr .x1).toNat ≤ 256)
    (hp : InRegions s₀.wr (s₀.gpr .x0) 256)
    (hk : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x17) (s₀.gpr .x1).toNat)
    (hs : Mem.Sep (s₀.gpr .x17) (s₀.gpr .x1).toNat (s₀.gpr .x0) 256)
    (h : ScheduleInv s₀ r s) :
    WP isa (.loop scheduleStep (.nonzero .x .x11)) s (ScheduleInv s₀ 256) := by
  refine WP.loop (M := isa) (fun rem t => ∃ j, j < 256 ∧ rem = 256 - j ∧ ScheduleInv s₀ j t)
    ?_ (256 - r) s ⟨r, hr, rfl, h⟩
  intro rem t ⟨j, hj, hrem, ht⟩
  refine WP.mono (schedule_inv_step s₀ t j hj hlen hp hk hs ht) fun u ⟨hu, hz⟩ => ?_
  by_cases hend : j + 1 = 256
  · left
    refine ⟨?_, hend ▸ hu⟩
    simp [eval, State.read, hz, hend]
  · right
    have hnz : BitVec.ofNat 64 (j + 1) - 256#64 ≠ 0#64 := by bv_omega
    refine ⟨?_, 256 - (j + 1), by omega, j + 1, by omega, rfl, hu⟩
    simp only [eval, State.read, BitVec.setWidth_eq, hz, bne, BitVec.ofNat_eq_ofNat,
      beq_eq_false_iff_ne.mpr hnz]
    rfl

end VG.Proof.Rc4.AArch64
