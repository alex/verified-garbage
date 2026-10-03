import VerifiedGarbage.Proof.Curve448.AArch64.Fast.ColEnd

/-!
# The end of a product: the last carries and the result

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside write8_eq read8_eq limbs)
open VG.Proof.Ed25519.AArch64 (read_x)

theorem read8_eq_word (m : Mem) (base : Addr) (d : Nat) :
    m.read (base + BitVec.ofNat 64 d) 8 = word m base d := by
  simp only [word, off, Mem.readW, BitVec.setWidth_eq]

theorem word_writeW (m : Mem) (base : Addr) {d d' : Nat} (hd : d + 8 ≤ 8192) (hd' : d' + 8 ≤ 8192)
    (h : d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') (v : BitVec 64) :
    word (m.writeW (off base d) v) base d' = if d' = d then v else word m base d' := by
  by_cases e : d' = d
  · rw [ite_eq_left e, e, word, Mem.readW_writeW_self64]
  · rw [ite_eq_right e]
    exact Mem.readW_writeW_sep (Offset.sep base (by omega) (by omega) (by omega)) (by decide)

theorem readW_writeW' (m : Mem) (base : Addr) {d d' : Nat} (hd : d + 8 ≤ 8192)
    (hd' : d' + 8 ≤ 8192) (h : d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') (v : BitVec 64) :
    (m.writeW (base + BitVec.ofNat 64 d) v).readW (base + BitVec.ofNat 64 d') 64 =
      if d' = d then v else m.readW (base + BitVec.ofNat 64 d') 64 :=
  word_writeW m base hd hd' h v

theorem st_ok {s : State} {base : Addr} (hs : Scr s base) (r : Reg) {d : Nat}
    (h8 : d % 8 = 0) (hd : d + 8 ≤ 8192) :
    WP isa (.block [st r d]) s fun t =>
      t.mem = s.mem.writeW (off base d) (s.gpr r) ∧ Keeps [] s t := by
  have w := hs.write (d := d) (n := 8) hd
  have oe : d % 8 = 0 ∧ d < 32768 := ⟨h8, by omega⟩
  refine WP.of_runBlock ⟨_, by
    simp only [st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, read_x,
      State.store, oe, and_self, hs.x3, w, ite_true, Option.bind_some]; rfl, ?_⟩
  exact ⟨by simp only [BitVec.setWidth_eq, write8_eq], fun _ _ => rfl, rfl, rfl⟩

def finA : List Instr :=
  [.add .x .x4 .x4 CH, .add .x .x6 .x6 CH, .add .x .x6 .x6 CL,
    .lsr .x .x8 .x4 56, .logic .and .x .x4 .x4 MASK, .add .x .x5 .x5 .x8,
    .lsr .x .x8 .x6 56, .logic .and .x .x6 .x6 MASK, .add .x .x7 .x7 .x8]

theorem finA_ok (s : State) (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1))
    {l0 l1 l4 l5 cl ch : Nat} (h0 : (s.gpr .x4).toNat = l0) (h1 : (s.gpr .x5).toNat = l1)
    (h4 : (s.gpr .x6).toNat = l4) (h5 : (s.gpr .x7).toNat = l5)
    (hl : (s.gpr CL).toNat = cl) (hh : (s.gpr CH).toNat = ch)
    (c0 : l0 + ch < 2 ^ 64) (c4 : l4 + cl + ch < 2 ^ 64) (b1 : l1 < 2 ^ 56) (b5 : l5 < 2 ^ 56) :
    WP isa (.block finA) s fun t =>
      (t.gpr .x4).toNat = (l0 + ch) % radix ∧ (t.gpr .x5).toNat = l1 + (l0 + ch) / radix ∧
      (t.gpr .x6).toNat = (l4 + cl + ch) % radix ∧ (t.gpr .x7).toNat = l5 + (l4 + cl + ch) / radix ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [finA, runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 56 < 64 from by decide, ite_true]; rfl, ?_⟩
  have m56 : ∀ x : BitVec 64, (x &&& BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = x.toNat % radix := by
    intro x
    rw [BitVec.toNat_and, show (BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = 2 ^ 56 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    rfl
  simp only [CL, CH, MASK] at hm hl hh
  simp only [State.read, RegUpd.gpr_write, BitVec.setWidth_eq, CL, CH, MASK,
    reduceCtorEq, ite_true, ite_false, hm]
  refine ⟨?_, ?_, ?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · rw [m56, BitVec.toNat_add, h0, hh, Nat.mod_eq_of_lt c0]
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, h1, h0, hh,
      Nat.mod_eq_of_lt c0, Nat.shiftRight_eq_div_pow]
    simp only [radix]
    omega
  · rw [m56, BitVec.toNat_add, BitVec.toNat_add, h4, hh, hl,
      Nat.mod_eq_of_lt (by omega : l4 + ch < 2 ^ 64), Nat.mod_eq_of_lt (by omega : l4 + ch + cl < 2 ^ 64)]
    congr 1; omega
  · rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_add, h5, h4,
      hh, hl, Nat.mod_eq_of_lt (by omega : l4 + ch < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : l4 + ch + cl < 2 ^ 64), Nat.shiftRight_eq_div_pow]
    simp only [radix]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2, ite_false]

/-- The limbs that `finish` writes. -/
def finVal (l : Nat → Nat) (cl ch : Nat) (i : Nat) : Nat :=
  match i with
  | 0 => (l 0 + ch) % radix
  | 1 => l 1 + (l 0 + ch) / radix
  | 4 => (l 4 + cl + ch) % radix
  | 5 => l 5 + (l 4 + cl + ch) / radix
  | i => l i

theorem finish_split (o : Nat) : finish o =
    [ld .x4 o, ld .x5 (o + 8), ld .x6 (o + 32), ld .x7 (o + 40)] ++ finA ++
    [st .x4 o, st .x5 (o + 8), st .x6 (o + 32), st .x7 (o + 40)] := rfl

theorem finish_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 64 ≤ 8192)
    (ho8 : o % 8 = 0) (hm : s.gpr MASK = BitVec.ofNat 64 (2 ^ 56 - 1)) {l : Nat → Nat}
    (hl : ∀ i < 8, (word s.mem base (o + 8 * i)).toNat = l i) (hb : ∀ i < 8, l i < radix)
    {cl ch : Nat} (hcl : (s.gpr CL).toNat = cl) (hch : (s.gpr CH).toNat = ch)
    (c0 : l 0 + ch < 2 ^ 64) (c4 : l 4 + cl + ch < 2 ^ 64) :
    WP isa (.block (finish o)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = finVal l cl ch i) ∧ Outside base o 64 s.mem t.mem ∧
      Keeps [.x4, .x5, .x6, .x7, .x8] s t := by
  have rd : ∀ d, d + 8 ≤ 8192 → InRegions (s.rd ++ s.wr) (off base d) 8 := fun d hd => hs.read hd
  have ae : ∀ d, d % 8 = 0 → d + 8 ≤ 8192 → d % 8 = 0 ∧ d < 32768 := fun d h1 h2 => ⟨h1, by omega⟩
  rw [finish_split, List.append_assoc, WP.block_append_iff]
  refine WP.mono (WP.of_runBlock ⟨_, by
    simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes, State.load,
      RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
      reduceCtorEq, ite_false, hs.x3, ae o ho8 (by omega),
      ae (o + 8) (by omega) (by omega), ae (o + 32) (by omega) (by omega),
      ae (o + 40) (by omega) (by omega), and_self, ite_true,
      rd o (by omega), rd (o + 8) (by omega), rd (o + 32) (by omega),
      rd (o + 40) (by omega), Option.map_some, Option.bind_some]; rfl, rfl⟩) fun t ht => ?_
  subst ht
  rw [WP.block_append_iff]
  have wv : ∀ i < 8, (word s.mem base (o + 8 * i)).toNat = l i := hl
  refine WP.mono (finA_ok _ (by simp only [RegUpd.gpr_write, MASK, reduceCtorEq, ite_false]; exact hm)
    (l0 := l 0) (l1 := l 1) (l4 := l 4) (l5 := l 5)
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 0 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 1 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 4 (by decide))
    (by simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, read8_eq_word]; exact wv 5 (by decide))
    (by simp only [RegUpd.gpr_write, CL, reduceCtorEq, ite_false]; exact hcl)
    (by simp only [RegUpd.gpr_write, CH, reduceCtorEq, ite_false]; exact hch)
    c0 c4 (hb 1 (by decide)) (hb 5 (by decide))) fun u ⟨u4, u5, u6, u7, um, uk⟩ => ?_
  have u3 : u.gpr .x3 = base := by
    rw [uk.1 .x3 (by decide)]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
    exact hs.x3
  have u12 : u.gpr .x12 = 0x0fffffff := by
    rw [uk.1 .x12 (by decide)]
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]
    exact hs.mask
  have us : Scr u base := ⟨u3, u12, uk.2.2 ▸ hs.wr, hs.nowrap⟩
  have mu : u.mem = s.mem := um
  -- the four stores
  have sw : ∀ (t : State) (r : Reg) (d : Nat), Scr t base → d % 8 = 0 → d + 8 ≤ 8192 →
      WP isa (.block [st r d]) t fun t' =>
        (∀ d', d' + 8 ≤ 8192 → (d' = d ∨ d' + 8 ≤ d ∨ d + 8 ≤ d') →
          word t'.mem base d' = if d' = d then t.gpr r else word t.mem base d') ∧
        Outside base d 8 t.mem t'.mem ∧ t'.gpr = t.gpr ∧ t'.rd = t.rd ∧ t'.wr = t.wr := by
    intro t r d ht h8 hd
    refine WP.mono (st_ok ht r h8 hd) fun t' ⟨hm, hk⟩ => ⟨fun d' hd' hs => ?_, ?_, ?_, hk.2.1, hk.2.2⟩
    · rw [hm]; exact word_writeW _ _ hd hd' hs _
    · rw [hm]; exact writeW_outside _ _ _ hd
    · funext q; exact hk.1 q (by simp)
  rw [show ([st .x4 o, st .x5 (o + 8), st .x6 (o + 32), st .x7 (o + 40)] : List Instr) =
      [st .x4 o] ++ [st .x5 (o + 8)] ++ [st .x6 (o + 32)] ++ [st .x7 (o + 40)] from rfl]
  simp only [List.append_assoc]
  have ss : ∀ t : State, t.gpr .x3 = base → t.gpr .x12 = 0x0fffffff → t.wr = u.wr → Scr t base :=
    fun t h1 h2 h3 => ⟨h1, h2, h3 ▸ us.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (sw u .x4 (o) us (by omega) (by omega)) fun t1 ⟨t1w, t1o, t1g, t1r, t1wr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sw t1 .x5 (o + 8) (ss t1 (by simp only [*]) (by simp only [*]) (by simp only [*])) (by omega) (by omega)) fun t2 ⟨t2w, t2o, t2g, t2r, t2wr⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (sw t2 .x6 (o + 32) (ss t2 (by simp only [*]) (by simp only [*]) (by simp only [*])) (by omega) (by omega)) fun t3 ⟨t3w, t3o, t3g, t3r, t3wr⟩ => ?_
  refine WP.mono (sw t3 .x7 (o + 40) (ss t3 (by simp only [*]) (by simp only [*]) (by simp only [*])) (by omega) (by omega)) fun t4 ⟨t4w, t4o, t4g, t4r, t4wr⟩ => ?_
  have keep : ∀ d, d + 8 ≤ 8192 → (d + 8 ≤ o ∨ o + 8 ≤ d) → (d + 8 ≤ o + 8 ∨ o + 16 ≤ d) →
      (d + 8 ≤ o + 32 ∨ o + 40 ≤ d) → (d + 8 ≤ o + 40 ∨ o + 48 ≤ d) →
      word t4.mem base d = word s.mem base d := by
    intro d hd h1 h2 h3 h4
    rw [t4w d hd (by omega), ite_eq_right (by omega), t3w d hd (by omega), ite_eq_right (by omega),
      t2w d hd (by omega), ite_eq_right (by omega), t1w d hd (by omega), ite_eq_right (by omega), mu]
  refine ⟨fun i hi => ?_, ?_, ?_⟩
  · obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
        i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    · change (word t4.mem base (o)).toNat = _
      rw [t4w (o) (by omega) (by omega), ite_eq_right (by omega), t3w (o) (by omega) (by omega), ite_eq_right (by omega), t2w (o) (by omega) (by omega), ite_eq_right (by omega), t1w (o) (by omega) (by omega), ite_eq_left rfl]
      rw [u4]; rfl
    · change (word t4.mem base (o + 8)).toNat = _
      rw [t4w (o + 8) (by omega) (by omega), ite_eq_right (by omega), t3w (o + 8) (by omega) (by omega), ite_eq_right (by omega), t2w (o + 8) (by omega) (by omega), ite_eq_left rfl]
      rw [t1g]
      rw [u5]; rfl
    · change (word t4.mem base (o + 16)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 2 (by decide)
    · change (word t4.mem base (o + 24)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 3 (by decide)
    · change (word t4.mem base (o + 32)).toNat = _
      rw [t4w (o + 32) (by omega) (by omega), ite_eq_right (by omega), t3w (o + 32) (by omega) (by omega), ite_eq_left rfl]
      rw [t2g, t1g]
      rw [u6]; rfl
    · change (word t4.mem base (o + 40)).toNat = _
      rw [t4w (o + 40) (by omega) (by omega), ite_eq_left rfl]
      rw [t3g, t2g, t1g]
      rw [u7]; rfl
    · change (word t4.mem base (o + 48)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 6 (by decide)
    · change (word t4.mem base (o + 56)).toNat = _
      rw [keep _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hl 7 (by decide)
  · rw [← mu]
    have w : ∀ {m m' : Mem} {d : Nat}, Outside base d 8 m m' → o ≤ d → d + 8 ≤ o + 64 →
        Outside base o 64 m m' := fun h h1 h2 => h.mono h1 h2
    exact (w t1o (by omega) (by omega)).trans ((w t2o (by omega) (by omega)).trans
      ((w t3o (by omega) (by omega)).trans (w t4o (by omega) (by omega))))
  · refine ⟨fun q hq => ?_, ?_, ?_⟩
    · rw [t4g, t3g, t2g, t1g, uk.1 q hq]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
      simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, ite_false]
    · rw [t4r, t3r, t2r, t1r, uk.2.1]; rfl
    · rw [t4wr, t3wr, t2wr, t1wr, uk.2.2]; rfl

end VG.Proof.Curve448.AArch64.Fast
