import VerifiedGarbage.Proof.Rc4.AArch64.Row

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 RegUpd

/-- Memory after the first `r` rows have been visited. -/
def PrefixMem (m : Mem) (p : Addr) (idx value : Byte) (r : Nat) : Mem :=
  if idx.toNat < 16 * r then m.write (p + BitVec.ofNat 64 idx.toNat) 1 value else m

theorem prefix_read (m : Mem) (p : Addr) (idx value : Byte) (r : Nat) (hr : r < 16) :
    (PrefixMem m p idx value r).read (p + BitVec.ofNat 64 (16 * r)) 16 =
      m.read (p + BitVec.ofNat 64 (16 * r)) 16 := by
  unfold PrefixMem
  by_cases h : idx.toNat < 16 * r
  · rw [ite_eq_left h]
    exact Mem.read_write_sep (Offset.sep p (.inr (by omega)) (by omega) (by omega)) (by decide)
  · rw [ite_eq_right h]

theorem prefix_store (m : Mem) (p : Addr) (idx value : Byte) (r : Nat) (hr : r < 16) :
    (PrefixMem m p idx value r).write (p + BitVec.ofNat 64 (16 * r)) 16
      (replaceVector (m.read (p + BitVec.ofNat 64 (16 * r)) 16)
        (idx - BitVec.ofNat 8 (16 * r)) value) = PrefixMem m p idx value (r + 1) := by
  rw [← prefix_read m p idx value r hr, write_row _ _ _ _ _ hr]
  unfold PrefixMem
  by_cases h : idx.toNat < 16 * r
  · simp only [ite_eq_left h, ite_eq_left (show idx.toNat < 16 * (r + 1) by omega),
      ite_eq_right (show ¬ (16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1)) by omega)]
  · by_cases hn : idx.toNat < 16 * (r + 1)
    · simp only [ite_eq_right h, ite_eq_left hn,
        ite_eq_left (show 16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1) by omega)]
    · simp only [ite_eq_right h, ite_eq_right hn,
        ite_eq_right (show ¬ (16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1)) by omega)]

def ReplaceInv (s₀ : State) (idx value : Byte) (r : Nat) (s : State) : Prop :=
  Keep s₀ s ∧ s.mem = PrefixMem s₀.mem (s₀.gpr .x0) idx value r ∧
    s.gpr .x5 = BitVec.ofNat 64 (16 * r) ∧
    s.gpr .x6 = Acc s₀.mem (s₀.gpr .x0) idx r ∧ s.gpr .x9 = 255#64 ∧
    s.gpr .x16 = 0x01010101#64 ∧ s.v .v3 = laneIndices ∧
    s.v .v4 = eqTable ∧ s.v .v5 = repeatByte value

theorem replace_setup (s : State) (idx value : Byte)
    (hvalue : s.gpr .x14 = value.setWidth 64) :
    WP isa (.block replaceSetup) s (ReplaceInv s idx value 0) := by
  have hcast : (value.setWidth 64).setWidth 32 = value.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have h32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have hlanes : ofVWords 0x03020100#32 0x07060504#32 0x0b0a0908#32 0x0f0e0d0c#32 =
      laneIndices := by decide +kernel
  have heq : setLane 0#128 32 0 255#32 = eqTable := by decide +kernel
  have hmul : (257#16).setWidth 32 &&& ~~~(65535#32 <<< 16) |||
      (257#16).setWidth 32 <<< 16 = 0x01010101#32 := by decide +kernel
  unfold replaceSetup
  refine WP.mono (keep (Q := fun t => t.mem = s.mem ∧ t.gpr .x5 = 0 ∧
      t.gpr .x6 = 0 ∧ t.gpr .x9 = 255#64 ∧ t.gpr .x16 = 0x01010101#64 ∧
      t.v .v3 = laneIndices ∧ t.v .v4 = eqTable ∧ t.v .v5 = repeatByte value) ?_ (by rfl)) ?_
  · rrun [hvalue, hcast, h32, setLane_four, hlanes, heq, hmul, repeat_words]
  · intro t ⟨⟨hm, hx, ha, hmask, hmul, hl, he, hv⟩, hk⟩
    refine ⟨hk, ?_, ?_, ?_, hmask, hmul, hl, he, hv⟩
    · simpa [PrefixMem] using hm
    · simpa using hx
    · simpa [Acc] using ha

theorem row_region (rs : List Region) (p : Addr) (r : Nat) (hr : r < 16)
    (hp : InRegions rs p 256) :
    InRegions rs (p + BitVec.ofNat 64 (16 * r)) 16 := by
  obtain ⟨region, hregion, hcontains⟩ := hp
  refine ⟨region, hregion, ?_⟩
  unfold Region.Contains at hcontains ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show 16 * r < 2 ^ 64 by omega)]
  have hmod := Nat.mod_le ((p - region.base).toNat + 16 * r) (2 ^ 64)
  omega

theorem mask32 (x : BitVec 32) :
    (x.setWidth 64 &&& 255#64).setWidth 32 = (x.setWidth 8).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hmask : (255#64 : BitVec 64).getLsbD k = decide (k < 8) := by
    change Nat.testBit 255 k = decide (k < 8)
    exact Nat.testBit_two_pow_sub_one 8 k
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, hmask, hk,
    show k < 64 by omega, decide_true, Bool.true_and]
  rw [Bool.and_comm]

theorem byte_offset (idx : Byte) (r : Nat) :
    (idx.setWidth 32 - BitVec.ofNat 32 (16 * r)).setWidth 8 =
      idx - BitVec.ofNat 8 (16 * r) := by bv_omega

theorem replace_step (s₀ s : State) (idx value : Byte) (r : Nat) (hr : r < 16)
    (hidx : s₀.gpr .x4 = idx.setWidth 64)
    (hp : InRegions s₀.wr (s₀.gpr .x0) 256)
    (h : ReplaceInv s₀ idx value r s) :
    WP isa (.block replaceStep) s fun t => ReplaceInv s₀ idx value (r + 1) t := by
  obtain ⟨hk, hm, hx, ha, hmask, hmul, hl, he, hv⟩ := h
  have h0 := hk.1 .x0 (by decide)
  have h4 := hk.1 .x4 (by decide)
  have hw : InRegions s.wr (s₀.gpr .x0 + BitVec.ofNat 64 (16 * r)) 16 := by
    rw [hk.2.2]
    exact row_region _ _ _ hr hp
  have hread : InRegions (s.rd ++ s.wr) (s₀.gpr .x0 + BitVec.ofNat 64 (16 * r)) 16 := by
    obtain ⟨region, hregion, hc⟩ := hw
    exact ⟨region, List.mem_append_right _ hregion, hc⟩
  have hoff : BitVec.ofNat 64 (16 * r) + 16#64 = BitVec.ofNat 64 (16 * (r + 1)) := by
    bv_omega
  have h32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
    (BitVec.setWidth_setWidth_of_le x (by decide)).trans (BitVec.setWidth_eq x)
  have hcast : (idx.setWidth 64).setWidth 32 = idx.setWidth 32 :=
    BitVec.setWidth_setWidth (by decide)
  have hrow : (BitVec.ofNat 64 (16 * r)).setWidth 32 = BitVec.ofNat 32 (16 * r) := by bv_omega
  have hindex : ((idx.setWidth 32 - BitVec.ofNat 32 (16 * r)).setWidth 64 &&& 255#64).setWidth 32 =
      (idx - BitVec.ofNat 8 (16 * r)).setWidth 32 := by rw [mask32, byte_offset]
  have hconst : (0x01010101#64).setWidth 32 = 0x01010101#32 := rfl
  unfold replaceStep
  refine WP.mono (keep (Q := fun t =>
      t.mem = PrefixMem s₀.mem (s₀.gpr .x0) idx value (r + 1) ∧
      t.gpr .x5 = BitVec.ofNat 64 (16 * (r + 1)) ∧
      t.gpr .x6 = Acc s₀.mem (s₀.gpr .x0) idx (r + 1) ∧ t.gpr .x9 = 255#64 ∧
      t.gpr .x16 = 0x01010101#64 ∧ t.v .v3 = laneIndices ∧
      t.v .v4 = eqTable ∧ t.v .v5 = repeatByte value) ?_ (by rfl)) ?_
  · rrun [State.store, h0, h4, hidx, hm, hx, ha, hmask, hmul, hl, he, hv,
      hread, hw, hcast, hrow, hoff, h32, hindex, hconst, repeat_words,
      mask_vector, prefix_read _ _ _ _ _ hr]
    constructor
    · exact prefix_store _ _ _ _ _ hr
    · rw [tbl_byte, row_byte _ _ _ _ hr]
      exact acc_succ _ _ _ _
  · intro t ⟨⟨hm', hx', ha', hmask', hmul', hl', he', hv'⟩, hk'⟩
    exact ⟨hk.trans hk', hm', hx', ha', hmask', hmul', hl', he', hv'⟩

theorem replace_scan (s₀ s : State) (idx value : Byte) (n r : Nat) (hr : r + n ≤ 16)
    (hidx : s₀.gpr .x4 = idx.setWidth 64)
    (hp : InRegions s₀.wr (s₀.gpr .x0) 256) (h : ReplaceInv s₀ idx value r s) :
    WP isa (scanRows replaceStep n) s (ReplaceInv s₀ idx value (r + n)) := by
  induction n generalizing r s with
  | zero => exact WP.block_nil h
  | succ n ih =>
    unfold scanRows
    refine WP.seq (WP.mono (replace_step s₀ s idx value r (by omega) hidx hp h) fun t ht => ?_)
    have he : r + (n + 1) = (r + 1) + n := by omega
    rw [he]
    exact ih t (r + 1) (by omega) ht

theorem replace_ok (s : State) (idx value : Byte)
    (hidx : s.gpr .x4 = idx.setWidth 64) (hvalue : s.gpr .x14 = value.setWidth 64)
    (hp : InRegions s.wr (s.gpr .x0) 256) :
    WP isa replace s fun t => Keep s t ∧
      t.mem = s.mem.write (s.gpr .x0 + BitVec.ofNat 64 idx.toNat) 1 value ∧
      t.gpr .x6 = (s.mem (s.gpr .x0 + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.gpr .x9 = 255#64 := by
  unfold replace
  refine WP.seq (WP.mono (replace_setup s idx value hvalue) fun t ht => ?_)
  refine WP.mono (replace_scan s t idx value 16 0 (by decide) hidx hp ht) fun u hu => ?_
  refine ⟨hu.1, ?_, ?_, hu.2.2.2.2.1⟩
  · simpa [PrefixMem, idx.isLt] using hu.2.1
  · simpa [Acc, idx.isLt] using hu.2.2.2.1

end VG.Proof.Rc4.AArch64
