import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
import VerifiedGarbage.Proof.MlDsa.Sample.ExpandMask
import VerifiedGarbage.Proof.MlDsa.Sample.LeWord
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball

/-!
# ML-DSA on AArch64: the loop of `vg_mldsa_sample_in_ball`

The polynomial `c` is kept in memory as the words that represent its
coefficients modulo `q` (`CStored`), from zeros; iteration `t` of the loop
over the 264 bytes after the sign bits does what `bStep` does to it and to `i`
(in `x10`, with `256 - i` in `x11`), with the sign bits not yet used in `x9`
(`step_ok`). The loop reads only the output, and writes only `c`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample.Ball

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_movk1 wp_addImm wp_subImm wp_strw
  wp_ldrw wp_ldrx wp_ldrb wp_sub wp_add wp_lsr wp_lsl wp_and wp_madd ptr_zero ptr_add toNat_sub_n
  toNat_add_n toNat_lsl_n toNat_byte toNat_lsr toNat_readW32 count_loop eval_zero eval_nonzero eq_zero_iff
  ne_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit movQ_ok q_eq)
open VG.Spec.MlDsa (coeffAt Zq q ofInt IPoly n)

/-- The polynomial `c` of `R` is stored at `p`, as elements of `ℤ_q`. -/
def CStored (m : Mem) (p : Addr) (c : IPoly) : Prop := ∀ k < 256, coeffAt m p k = zw (ofInt c[k]!)

/-- What the loop needs of the state it starts from: the 272 bytes `X` at
`bP = x25 + 840`, which it may read, zeros at `aP = x26`, which it may
write, and `τ` in `x27`. -/
structure LPre (X : List Byte) (bP aP : Addr) (τ : Nat) (s : State) : Prop where
  buf : ∀ p < 272, s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0
  inb : ∀ p < 272, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  inw : InRegions (s.rd ++ s.wr) bP 8
  ina : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  disj : (⟨bP, 272⟩ : Region).Disjoint (polyR aP)
  x25 : s.gpr .x25 + BitVec.ofNat 64 840 = bP
  x26 : s.gpr .x26 = aP
  x27 : (s.gpr .x27).toNat = τ
  tau : τ ≤ 256
  zero : ∀ i < 256, coeffAt s.mem aP i = 0

/-- The sign bits, as a `u64`. -/
abbrev W (X : List Byte) : BitVec 64 := BitVec.ofNat 64 (leNat (X.take 8))

/-- The polynomial and `i` after `t` iterations. -/
abbrev St (X : List Byte) (τ t : Nat) : IPoly × Nat :=
  bFold τ (signs X) (Vector.replicate n 0, 256 - τ) ((X.drop 8).take t)

/-- The registers the loop writes. -/
abbrev lRegs : List Reg := [.x2, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15]

/-- At the start of iteration `t`, from the loop's entry state `s₀`. -/
structure BAt (X : List Byte) (bP aP : Addr) (τ : Nat) (s₀ : State) (t : Nat) (s : State) : Prop where
  keep : Keep lRegs s₀ s
  frame : Frame [polyR aP] s₀.mem s.mem
  x2 : s.gpr .x2 = bP + BitVec.ofNat 64 (8 + t)
  x5 : (s.gpr .x5).toNat = 264 - t
  x9 : s.gpr .x9 = W X >>> ((St X τ t).2 - (256 - τ))
  x10 : (s.gpr .x10).toNat = (St X τ t).2
  x11 : (s.gpr .x11).toNat = 256 - (St X τ t).2
  x12 : (s.gpr .x12).toNat = q - 2
  x15 : (s.gpr .x15).toNat = 1
  st : CStored s.mem aP (St X τ t).1

theorem St_le (X : List Byte) (τ t : Nat) : (St X τ t).2 ≤ 256 := bFold_le (by simp) _

theorem St_ge (X : List Byte) (τ t : Nat) : 256 - τ ≤ (St X τ t).2 :=
  bFold_ge (τ := τ) (h := signs X) (Vector.replicate n 0, 256 - τ) _

theorem take_succ'' (L : List Byte) {i : Nat} (h : i < L.length) : L.take (i + 1) = L.take i ++ [L.getD i 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The sign bit of `i`. -/
theorem sign_bit {X : List Byte} {τ i : Nat} (hτ : τ ≤ 256) (hi0 : 256 - τ ≤ i) (hi : i < 256) (hτ' : τ ≤ 64) :
    (W X >>> (i - (256 - τ))).getLsbD 0 = (signs X).getD (i + τ - 256) false := by
  rw [BitVec.getLsbD_ushiftRight, Nat.add_zero, signs_getD, BitVec.getLsbD_ofNat,
    show i - (256 - τ) = i + τ - 256 by omega, decide_eq_true (show i + τ - 256 < 64 by omega), Bool.true_and]

/-- The word of the sign `b`, `1 + (q - 2) b`. -/
theorem sgn_word (x : BitVec 64) {v : BitVec 64} (hv : v.toNat = q - 2) {o : BitVec 64} (ho : o.toNat = 1) :
    (o + (x &&& o) * v).setWidth 32 = zw (ofInt (if x.getLsbD 0 then -1 else 1)) := by
  have hb : (x &&& o).toNat = if x.getLsbD 0 then 1 else 0 := by
    rw [BitVec.toNat_and, ho, show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      BitVec.getLsbD, Nat.testBit, Nat.shiftRight_zero, Nat.one_and_eq_mod_two]
    split <;> rename_i h <;> simp at h <;> omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, hb, hv, ho, zw_toNat]
  split <;> decide

/-- `c[i] ← c[j]`, `c[j] ← ±1` (with the sign bit 0 of `x9`), `i` incremented. -/
theorem set_ok {aP : Addr} {c : IPoly} {i j : Nat} (hij : j ≤ i) (hi : i < 256) {s : State}
    (h26 : s.gpr .x26 = aP) (h6 : (s.gpr .x6).toNat = j) (h10 : (s.gpr .x10).toNat = i)
    (h11 : (s.gpr .x11).toNat = 256 - i) (h12 : (s.gpr .x12).toNat = q - 2) (h15 : (s.gpr .x15).toNat = 1)
    (hw : ∀ k < 256, InRegions s.wr (coeffAddr aP k) 4) (hst : CStored s.mem aP c) :
    WP isa (.block bSet) s fun s' =>
      Keep [.x8, .x13, .x14, .x9, .x10, .x11] s s' ∧ (s'.gpr .x10).toNat = i + 1 ∧ (s'.gpr .x11).toNat = 256 - (i + 1) ∧
      s'.gpr .x9 = s.gpr .x9 >>> 1 ∧
      CStored s'.mem aP ((c.set! i c[j]!).set! j (if (s.gpr .x9).getLsbD 0 then -1 else 1)) ∧
      Frame [polyR aP] s.mem s'.mem := by
  have addr : ∀ {x : BitVec 64} {k : Nat}, x.toNat = k → k < 256 → aP + x <<< 2 = coeffAddr aP k :=
    fun {x k} hx hk => by
      rw [coeffAddr]; congr 1; apply BitVec.eq_of_toNat_eq
      rw [toNat_lsl_n (by rw [hx]; simp only [Nat.reducePow]; omega), hx, BitVec.toNat_ofNat]; omega
  refine wp_lsl (by decide) fun s₁ o₁ e₁ => wp_add fun s₂ o₂ e₂ => wp_lsl (by decide) fun s₃ o₃ e₃ =>
    wp_add fun s₄ o₄ e₄ => ?_
  have a8 : s₄.gpr .x8 = coeffAddr aP j := by
    rw [o₄.get .x8, o₃.get .x8, e₂, o₁.get .x26, h26, e₁]; exact addr h6 (by omega)
  have a13 : s₄.gpr .x13 = coeffAddr aP i := by
    rw [e₄, o₃.get .x26, o₂.get .x26, o₁.get .x26, h26, e₃, o₂.get .x10, o₁.get .x10]; exact addr h10 hi
  have w4 : s₄.wr = s.wr := by rw [o₄.wr, o₃.wr, o₂.wr, o₁.wr]
  have r4 : s₄.rd = s.rd := by rw [o₄.rd, o₃.rd, o₂.rd, o₁.rd]
  have m4 : s₄.mem = s.mem := by rw [o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  refine wp_ldrw (a := coeffAddr aP j) (by decide) (by rw [a8, ptr_zero])
    (by rw [r4, w4]; exact Proof.MlKem.AArch64.in_rd_wr (hw j (by omega))) fun s₅ o₅ e₅ => ?_
  refine wp_strw (a := coeffAddr aP i) (by decide) (by rw [o₅.get .x13, a13, ptr_zero])
    (by rw [o₅.wr, w4]; exact hw i hi) fun s₆ o₆ => ?_
  refine wp_and fun s₇ o₇ e₇ => wp_madd fun s₈ o₈ e₈ => ?_
  refine wp_strw (a := coeffAddr aP j) (by decide)
    (by rw [o₈.get .x8, o₇.get .x8, o₆.gpr, o₅.get .x8, a8, ptr_zero])
    (by rw [o₈.wr, o₇.wr, o₆.wr, o₅.wr, w4]; exact hw j (by omega)) fun s₉ o₉ => ?_
  refine wp_lsr (by decide) fun s₁₀ o₁₀ e₁₀ => wp_addImm (by decide) fun s₁₁ o₁₁ e₁₁ =>
    wp_subImm (by decide) fun s₁₂ o₁₂ e₁₂ => wp_nil ?_
  have k₈ := (((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep).trans o₈.keep).mono (rs' := [.x8, .x13, .x14]) (by decide)
  have k₅ := ((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).mono
    (rs' := [.x8, .x13, .x14]) (by decide)
  have v14 : s₈.gpr .x14 = s.gpr .x15 + (s.gpr .x9 &&& s.gpr .x15) * s.gpr .x12 := by
    rw [e₈, o₇.get .x15, o₇.get .x12, e₇, o₆.gpr, k₅.get .x9, k₅.get .x15, k₅.get .x12]
  have m₉ : s₉.mem = (s.mem.writeW (coeffAddr aP i) (s.mem.readW (coeffAddr aP j) 32)).writeW
      (coeffAddr aP j) (zw (ofInt (if (s.gpr .x9).getLsbD 0 then -1 else 1))) := by
    rw [o₉.mem, o₈.mem, o₇.mem, o₆.mem, v14, sgn_word _ h12 h15, e₅, o₅.mem, m4]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_setWidth, toNat_readW32, Nat.mod_eq_of_lt (s.mem.readW _ 32).isLt]
  have k₁₂ := (((((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans
    o₆.keep).trans o₇.keep).trans o₈.keep).trans o₉.keep).trans o₁₀.keep).trans o₁₁.keep).trans
    o₁₂.keep).mono (rs' := [.x8, .x13, .x14, .x9, .x10, .x11]) (by decide)
  have m₁₂ : s₁₂.mem = s₉.mem := by rw [o₁₂.mem, o₁₁.mem, o₁₀.mem]
  refine ⟨k₁₂, ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [o₁₂.get .x10, e₁₁, o₁₀.get .x10, o₉.gpr, k₈.get .x10, toNat_add_n (by rw [h10]; simp; omega), h10]; rfl
  · rw [e₁₂, o₁₁.get .x11, o₁₀.get .x11, o₉.gpr, k₈.get .x11, toNat_sub_n (by rw [h11]; simp; omega),
      h11]; simp; omega
  · rw [o₁₂.get .x9, o₁₁.get .x9, e₁₀, o₉.gpr, k₈.get .x9]
  · rw [m₁₂, m₉, coeffAt_writeW _ _ hk (by omega), coeffAt_writeW _ _ hk hi,
      ipoly_set!_get _ _ (by simp only [n]; omega), ipoly_set!_get _ _ (by simp only [n]; omega)]
    by_cases ejk : j = k
    · subst ejk; rw [ifT rfl, ifT rfl]
    · rw [ifF ejk, ifF ejk]
      by_cases eik : i = k
      · subst eik; rw [ifT rfl, ifT rfl, ← coeffAt_eq, hst j (by omega)]
      · rw [ifF eik, ifF eik]; exact hst k hk
  · rw [m₁₂, m₉]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hi)).writeW
      (List.mem_singleton_self _) _ (coeff_contains _ (by omega))


end VG.Proof.MlDsa.AArch64.Sample.Ball

namespace VG.Proof.MlDsa.AArch64.Sample.Ball

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_ldrx wp_ldrb wp_sub
  wp_lsr ptr_zero ptr_add toNat_sub_n toNat_byte toNat_lsr count_loop eval_zero eval_nonzero eq_zero_iff
  ne_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit movQ_ok q_eq)
open VG.Spec.MlDsa (coeffAt Zq q ofInt IPoly n)

/-- The byte `p` of the output, in any state of the loop. -/
theorem BAt.byte {X : List Byte} {bP aP : Addr} {τ : Nat} {s₀ : State} (hp : LPre X bP aP τ s₀) {t : Nat}
    {s : State} (h : BAt X bP aP τ s₀ t s) {p : Nat} (hp' : p < 272) :
    s.mem (bP + BitVec.ofNat 64 p) = X.getD p 0 := by
  rw [← hp.buf p hp']
  exact h.frame _ fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact hp.disj _ (Offset.contains_base _ (by omega) (by omega))

/-- An iteration, from `BAt t`. -/
theorem step_ok {X : List Byte} (hX : X.length = 272) {bP aP : Addr} {τ : Nat} (hτ : τ ≤ 64) {s₀ : State}
    (hp : LPre X bP aP τ s₀) {t : Nat} (ht : t < 264) {s : State} (h : BAt X bP aP τ s₀ t s) :
    WP isa bBody s fun s' => BAt X bP aP τ s₀ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 264) := by
  have hle := St_le X τ t
  have hge := St_ge X τ t
  have hj : ((X.drop 8).getD t 0) = X.getD (8 + t) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have ht1 : St X τ (t + 1) = bStep τ (signs X) (St X τ t) ((X.drop 8).getD t 0) := by
    simp only [St]
    rw [take_succ'' _ (by rw [List.length_drop, hX]; omega), bFold_snoc]
  have hw : ∀ k < 256, InRegions s.wr (coeffAddr aP k) 4 := fun k hk => by rw [h.keep.wr]; exact hp.ina k hk
  -- the tail of the iteration
  have tail : ∀ u : State, Keep [.x6, .x7, .x8, .x13, .x14, .x9, .x10, .x11] s u → Frame [polyR aP] s.mem u.mem →
      u.gpr .x9 = W X >>> ((St X τ (t + 1)).2 - (256 - τ)) → (u.gpr .x10).toNat = (St X τ (t + 1)).2 →
      (u.gpr .x11).toNat = 256 - (St X τ (t + 1)).2 → CStored u.mem aP (St X τ (t + 1)).1 →
      WP isa (.block [.addImm .x .x2 .x2 1, .subImm .x .x5 .x5 1]) u fun s' =>
        BAt X bP aP τ s₀ (t + 1) s' ∧ ((s'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 264) := by
    intro u ku fu x9 x10 x11 st
    refine wp_addImm (by decide) fun u₁ o₁ e₁ => wp_subImm (by decide) fun u₂ o₂ e₂ => wp_nil ?_
    have c5 : (u₁.gpr .x5).toNat = 264 - t := by rw [o₁.get .x5, ku.get .x5, h.x5]
    have v5 : (u₂.gpr .x5).toNat = 264 - (t + 1) := by
      rw [e₂, toNat_sub_n (by rw [c5]; simp; omega), c5]; simp; omega
    refine ⟨⟨((h.keep.trans ku).trans (o₁.keep.trans o₂.keep)).mono, h.frame.trans (by
        rw [o₂.mem, o₁.mem]; exact fu), ?_, v5, by rw [o₂.get .x9, o₁.get .x9, x9],
      by rw [o₂.get .x10, o₁.get .x10, x10], by rw [o₂.get .x11, o₁.get .x11, x11],
      by rw [o₂.get .x12, o₁.get .x12, ku.get .x12, h.x12], by rw [o₂.get .x15, o₁.get .x15, ku.get .x15, h.x15],
      by rw [o₂.mem, o₁.mem]; exact st⟩, by rw [v5]; omega⟩
    rw [o₂.get .x2, e₁, ku.get .x2, h.x2, ptr_add, Nat.add_assoc]
  by_cases hf : (St X τ t).2 = 256
  · -- `i = 256`: nothing to do
    have e : St X τ (t + 1) = St X τ t := by rw [ht1, bStep_full (by simp only [n]; omega)]
    refine WP.seq (WP.ite true (by rw [eval_zero, eq_zero_iff, h.x11, hf]; rfl) (fun _ => wp_nil ?_)
      (fun h => nomatch h))
    exact tail s (Keep.refl _ _) (Frame.refl _ _) (by rw [e, h.x9]) (by rw [e, h.x10]) (by rw [e, h.x11])
      (by rw [e]; exact h.st)
  refine WP.seq (WP.ite false (by rw [eval_zero, eq_zero_iff, h.x11]; simp; omega) (fun h => nomatch h)
    fun _ => ?_)
  have hin : InRegions (s.rd ++ s.wr) (s.gpr .x2) 1 := by
    rw [h.keep.rd, h.keep.wr, h.x2]; exact hp.inb _ (by omega)
  have hb : s.mem (s.gpr .x2) = (X.drop 8).getD t 0 := by rw [hj, h.x2]; exact h.byte hp (by omega)
  refine WP.seq (wp_ldrb (a := s.gpr .x2) (by decide) (ptr_zero _) hin fun s₁ o₁ e₁ =>
    wp_sub fun s₂ o₂ e₂ => wp_lsr (by decide) fun s₃ o₃ e₃ => wp_nil ?_)
  have k₃ := ((o₁.keep.trans o₂.keep).trans o₃.keep).mono (rs' := [.x6, .x7]) (by decide)
  have v6 : (s₃.gpr .x6).toNat = ((X.drop 8).getD t 0).toNat := by
    rw [o₃.get .x6, o₂.get .x6, e₁, toNat_byte, hb]
  have hjl := ((X.drop 8).getD t 0).isLt
  have v7 : (s₃.gpr .x7).toNat = if (St X τ t).2 < ((X.drop 8).getD t 0).toNat then 1 else 0 := by
    rw [e₃, e₂, o₁.get .x10]
    exact lt_bit h.x10 (by rw [e₁, toNat_byte, hb])
      (by omega) (by simp only [Nat.reducePow] at hjl ⊢; omega)
  have hi : (St X τ t).2 < n := by simp only [n]; omega
  by_cases hr : (St X τ t).2 < ((X.drop 8).getD t 0).toNat
  · -- rejected
    have e : St X τ (t + 1) = St X τ t := by
      rw [ht1]; unfold bStep; rw [ifT hi, ifT hr]
    refine WP.ite true (by rw [eval_nonzero, ne_zero_iff, v7, ifT hr]; rfl) (fun _ => wp_nil ?_)
      (fun h => nomatch h)
    exact tail s₃ k₃.mono (by rw [o₃.mem, o₂.mem, o₁.mem]; exact Frame.refl _ _)
      (by rw [e, k₃.get .x9, h.x9]) (by rw [e, k₃.get .x10, h.x10]) (by rw [e, k₃.get .x11, h.x11])
      (by rw [e, o₃.mem, o₂.mem, o₁.mem]; exact h.st)
  · -- a coefficient set
    have e : St X τ (t + 1) = (((St X τ t).1.set! (St X τ t).2 (St X τ t).1[((X.drop 8).getD t 0).toNat]!).set!
        ((X.drop 8).getD t 0).toNat (if (signs X).getD ((St X τ t).2 + τ - 256) false then -1 else 1),
        (St X τ t).2 + 1) := by
      rw [ht1]; unfold bStep; rw [ifT hi, ifF hr]
    refine WP.ite false (by rw [eval_nonzero, ne_zero_iff, v7, ifF hr]; rfl) (fun h => nomatch h)
      (fun _ => WP.mono (set_ok (aP := aP) (c := (St X τ t).1) (i := (St X τ t).2)
        (j := ((X.drop 8).getD t 0).toNat) (by omega) (by omega)
        (by rw [k₃.get .x26, h.keep.get .x26, hp.x26]) v6 (by rw [k₃.get .x10, h.x10])
        (by rw [k₃.get .x11, h.x11]) (by rw [k₃.get .x12, h.x12]) (by rw [k₃.get .x15, h.x15])
        (by rw [o₃.wr, o₂.wr, o₁.wr]; exact hw) (by rw [o₃.mem, o₂.mem, o₁.mem]; exact h.st))
        fun s₄ ⟨k₄, x10, x11, x9, st, f₄⟩ => ?_)
    have sg : (s₃.gpr .x9).getLsbD 0 = (signs X).getD ((St X τ t).2 + τ - 256) false := by
      rw [k₃.get .x9, h.x9]; exact sign_bit (by omega) hge (by omega) hτ
    rw [sg] at st
    refine tail s₄ (k₃.trans k₄).mono (by rw [← show s₃.mem = s.mem by rw [o₃.mem, o₂.mem, o₁.mem]]; exact f₄) ?_
      (by rw [e, x10]) (by rw [e, x11]) (by rw [e]; exact st)
    rw [x9, k₃.get .x9, h.x9, e, ← BitVec.shiftRight_add, show (St X τ t).2 + 1 - (256 - τ) =
      (St X τ t).2 - (256 - τ) + 1 by omega]

/-- The loop: `BAt 264` at the end. -/
theorem loop_ok {X : List Byte} (hX : X.length = 272) {bP aP : Addr} {τ : Nat} (hτ : τ ≤ 64) {s₀ : State}
    (hp : LPre X bP aP τ s₀) : WP isa bLoop s₀ (BAt X bP aP τ s₀ 264) := by
  unfold bLoop bSetup movQ
  simp only [List.cons_append, List.nil_append]
  refine WP.seq (wp_ldrx (a := bP) (by decide) hp.x25 hp.inw fun s₁ o₁ e₁ => wp_movz fun s₂ o₂ e₂ =>
    wp_sub fun s₃ o₃ e₃ => wp_mov fun s₄ o₄ e₄ => wp_addImm (by decide) fun s₅ o₅ e₅ =>
    wp_movz fun s₆ o₆ e₆ => movQ_ok fun s₇ o₇ e₇ => wp_subImm (by decide) fun s₈ o₈ e₈ =>
    wp_movz fun s₉ o₉ e₉ => wp_nil ?_)
  have k₉ := ((((((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep).trans o₈.keep).trans o₉.keep)
  have m₉ : s₉.mem = s₀.mem := by
    rw [o₉.mem, o₈.mem, o₇.mem, o₆.mem, o₅.mem, o₄.mem, o₃.mem, o₂.mem, o₁.mem]
  have hS : St X τ 0 = (Vector.replicate n 0, 256 - τ) := rfl
  have x27 : s₂.gpr .x27 = s₀.gpr .x27 := by rw [o₂.get .x27, o₁.get .x27]
  have i₀ : BAt X bP aP τ s₀ 0 s₉ := ⟨k₉.mono, by rw [m₉]; exact Frame.refl _ _,
    by rw [o₉.get .x2, o₈.get .x2, o₇.get .x2, o₆.get .x2, e₅, o₄.get .x25, o₃.get .x25, o₂.get .x25,
      o₁.get .x25, ← hp.x25, ptr_add],
    by rw [o₉.get .x5, o₈.get .x5, o₇.get .x5, e₆]; rfl,
    by rw [o₉.get .x9, o₈.get .x9, o₇.get .x9, o₆.get .x9, o₅.get .x9, o₄.get .x9, o₃.get .x9, o₂.get .x9, e₁,
      hS, Nat.sub_self, BitVec.ushiftRight_zero]
       exact readW_leNat _ _ _ fun k hk => hp.buf k (by omega),
    by rw [o₉.get .x10, o₈.get .x10, o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, e₃,
      BitVec.toNat_sub, e₂, x27, hp.x27, hS]; simp; omega,
    by rw [o₉.get .x11, o₈.get .x11, o₇.get .x11, o₆.get .x11, o₅.get .x11, e₄, o₃.get .x27, x27, hp.x27, hS]
       simp only; have := hp.tau; omega,
    by rw [o₉.get .x12, e₈, toNat_sub_n (by rw [e₇, q_eq]; decide), e₇, q_eq]; rfl,
    by rw [e₉]; rfl,
    by rw [m₉, hS]; intro k hk
       rw [hp.zero k hk, getElem!_pos _ k (by simp only [n]; omega), Vector.getElem_replicate]; rfl⟩
  exact count_loop (by decide) (BAt X bP aP τ s₀) (fun t ht s h => step_ok hX hτ hp ht h) i₀

end VG.Proof.MlDsa.AArch64.Sample.Ball
