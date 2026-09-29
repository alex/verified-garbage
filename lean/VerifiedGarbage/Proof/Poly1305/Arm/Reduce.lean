import VerifiedGarbage.Proof.Poly1305.Arm.Common
import VerifiedGarbage.Proof.Framework.PowLit

section

/-!
# Poly1305 on 32-bit ARM: adding the limbs of four words to the columns

Untrusted: everything here is checked by Lean. `addWords` adds limbs 0–8 of
the 16 bytes at `r1` to `r3`–`r11`, piece by piece (`piece_ok`), and leaves
the last word in `r2` (`addWords_ok`); as numbers, the limbs are `mlimb`.
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- What piece `p` of the word `w` adds to its column. -/
def pieceBV (w : BitVec 32) : Nat × Nat × Nat → BitVec 32
  | (_, 0, b) => w >>> b
  | (_, a, b) => (w <<< a) >>> b

/-- What the pieces `l` of the word `w` add to column `k`. -/
def contrib : List (Nat × Nat × Nat) → Nat → BitVec 32 → BitVec 32
  | [], _, _ => 0
  | p :: ps, k, w => (if p.1 = k then pieceBV w p else 0) + contrib ps k w

/-- The columns' registers. -/
def yregs : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11]

theorem yr_yregs : ∀ k < 9, yr k ∈ yregs := by decide +kernel

theorem zadd (x : BitVec 32) : 0 + x = x := by simp
theorem addz (x : BitVec 32) : x + 0 = x := by simp

theorem piece_ok (p : Nat × Nat × Nat) (hk : p.1 < 9) (ha : p.2.1 ≤ 31) (hb : 1 ≤ p.2.2 ∧ p.2.2 ≤ 31)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', s'.gpr (yr p.1) = s.gpr (yr p.1) + pieceBV (s.gpr .r2) p →
      Keeps [yr p.1, .r12] s s' → WP isa (.block rest) s' Q) :
    WP isa (.block (piece p ++ rest)) s Q := by
  obtain ⟨c, a, b⟩ := p
  simp only at hk ha hb k
  have hne := yr_ne c hk
  cases a with
  | zero =>
    simp only [piece, List.cons_append, List.nil_append]
    exact wp_add (op2_lsr hb) fun s1 u1 => k s1 u1.gpr (u1.keeps (by simp))
  | succ a =>
    simp only [piece, List.cons_append, List.nil_append]
    refine wp_mov (op2_lsl ⟨by omega, ha⟩) fun s1 u1 => wp_add (op2_lsr hb) fun s2 u2 => ?_
    refine k s2 ?_ ((u1.keeps (by simp)).trans (u2.keeps (by simp)))
    rw [u2.gpr, u1.gpr, u1.other _ hne.2.2.2]
    rfl

theorem pieces_ok (l : List (Nat × Nat × Nat))
    (hl : ∀ p ∈ l, p.1 < 9 ∧ p.2.1 ≤ 31 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 31)
    {rest : List Instr} {s : State} {Q : State → Prop}
    (k : ∀ s', (∀ j < 9, s'.gpr (yr j) = s.gpr (yr j) + contrib l j (s.gpr .r2)) →
      Keeps (.r12 :: yregs) s s' → WP isa (.block rest) s' Q) :
    WP isa (.block (l.flatMap piece ++ rest)) s Q := by
  induction l generalizing s with
  | nil => exact k s (fun j _ => by simp [contrib]) (Keeps.refl _ _)
  | cons p ps ih =>
    have hp := hl p List.mem_cons_self
    rw [List.flatMap_cons, List.append_assoc]
    refine piece_ok p hp.1 hp.2.1 hp.2.2 fun s1 h1 k1 => ?_
    refine ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) fun s2 h2 k2 => k s2 (fun j hj => ?_) ?_
    · have e2 : s1.gpr .r2 = s.gpr .r2 := k1.gpr _ (by have := yr_ne p.1 hp.1; simp [this.2.2.1.symm])
      rw [h2 j hj, e2, contrib]
      by_cases e : p.1 = j
      · subst e; rw [h1]; simp only [ite_true, BitVec.add_assoc]
      · have e1 : s1.gpr (yr j) = s.gpr (yr j) := k1.gpr _ (by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun h => e (yr_inj _ (by omega) _ (by omega) h).symm, (yr_ne j hj).2.2.2⟩)
        rw [e1]; simp only [e, ite_false, zadd]
    · exact (k1.mono fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact List.mem_cons_of_mem _ (yr_yregs _ hp.1)
        · exact List.mem_cons_self).trans k2

theorem pieces_valid : ∀ i < 4, ∀ p ∈ pieces i, p.1 < 9 ∧ p.2.1 ≤ 31 ∧ 1 ≤ p.2.2 ∧ p.2.2 ≤ 31 := by
  decide

/-- The words at `r1`. -/
def word (s : State) (i : Nat) : BitVec 32 :=
  s.mem.readW (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * i))) 32

/-- What words `0, …, i - 1` add to column `k`. -/
def wsum (w : Nat → BitVec 32) : Nat → Nat → BitVec 32
  | 0, _ => 0
  | i + 1, k => wsum w i k + contrib (pieces i) k (w i)

/-- After words `< i` (the registers relative to `s₀`). -/
structure WI (s₀ : State) (i : Nat) (s : State) : Prop where
  cols : ∀ j < 9, s.gpr (yr j) = s₀.gpr (yr j) + wsum (word s₀) i j
  r2 : 0 < i → s.gpr .r2 = word s₀ (i - 1)
  keeps : Keeps (.r2 :: .r12 :: yregs) s₀ s

theorem addWord_step {s₀ : State}
    (hin : ∀ i < 4, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4)
    (i : Nat) (s : State) (hi : i < 4) (h : WI s₀ i s) : WP isa (.block (addWord i)) s (WI s₀ (i + 1)) := by
  have e1 : s.gpr .r1 = s₀.gpr .r1 := h.keeps.gpr _ (by decide)
  rw [addWord, ← List.append_nil ((pieces i).flatMap piece)]
  refine wp_ldr (by omega) rfl (by rw [e1, h.keeps.rd, h.keeps.wr]; exact hin i hi) fun s1 u1 => ?_
  have hw : s1.gpr .r2 = word s₀ i := by rw [u1.gpr, e1, h.keeps.mem]; rfl
  refine pieces_ok _ (pieces_valid i hi) fun s2 h2 k2 => WP.block_nil ⟨fun j hj => ?_, fun _ => ?_, ?_⟩
  · rw [h2 j hj, hw, u1.other _ (yr_ne j hj).2.2.1, h.cols j hj, wsum, BitVec.add_assoc]
  · rw [k2.gpr _ (by decide), hw]; rfl
  · exact h.keeps.trans ((u1.keeps (by simp)).trans (k2.mono fun r hr => List.mem_cons_of_mem _ hr))

theorem addWords_ok {s₀ : State}
    (hin : ∀ i < 4, InRegions (s₀.rd ++ s₀.wr) (State.addr (s₀.gpr .r1 + BitVec.ofNat 32 (4 * i))) 4) :
    WP isa (.block addWords) s₀ fun s =>
      (∀ j < 9, s.gpr (yr j) = s₀.gpr (yr j) + wsum (word s₀) 4 j) ∧ s.gpr .r2 = word s₀ 3 ∧
      Keeps (.r2 :: .r12 :: yregs) s₀ s := by
  refine WP.mono (wp_range_flatMap (M := isa) (WI s₀) (addWord_step hin) 4 (Nat.le_refl _) s₀
    ⟨fun j _ => by simp [wsum], fun h => absurd h (by omega), Keeps.refl _ _⟩)
    fun s h => ⟨h.cols, h.r2 (by omega), h.keeps⟩

/-! ## The limbs as numbers -/

/-- The limbs `addWords` adds, as numbers. -/
theorem wsum_toNat (w : Nat → BitVec 32) {k : Nat} (hk : k < 9) :
    (wsum w 4 k).toNat = mlimb (w 0).toNat (w 1).toNat (w 2).toNat (w 3).toNat k := by
  have h0 := (w 0).isLt; have h1 := (w 1).isLt; have h2 := (w 2).isLt; have h3 := (w 3).isLt
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega
  all_goals simp only [wsum, contrib, pieces, pieceBV, mlimb, Nat.reduceEqDiff, ite_true, ite_false,
    zadd, addz, toNat_shr, toNat_shl]
  · omega
  · omega
  · rw [toNat_add_lt (by simp only [toNat_shl, toNat_shr]; omega)]; simp only [toNat_shl, toNat_shr]; omega
  · omega
  · rw [toNat_add_lt (by simp only [toNat_shl, toNat_shr]; omega)]; simp only [toNat_shl, toNat_shr]; omega
  · omega
  · omega
  · rw [toNat_add_lt (by simp only [toNat_shl, toNat_shr]; omega)]; simp only [toNat_shl, toNat_shr]; omega
  · omega

end VG.Proof.Poly1305.Arm

end

section

/-!
# Poly1305 on 32-bit ARM: carrying and the final reduction

Untrusted: everything here is checked by Lean. The columns (or limbs) are in
`r3`–`r11` and `r1` (`Cols`); `carryStep` moves a column's bits from 13 up
to the next column (`carries_ok`), `carryFold` carries them all into `fold`
(`carryFold_ok`), and `reduce` reduces them fully (`reduceRegs_ok`).
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- The columns (or limbs) are `v`, in `r3`–`r11` and `r1`. -/
def Cols (v : Nat → Nat) (s : State) : Prop := ∀ j < 10, (s.gpr (yr j)).toNat = v j

/-- The mask `movw r2, #0x1fff` leaves in `r2`. -/
abbrev maskV : BitVec 32 := (0x1fff#16).setWidth 32

/-- The registers of the columns. -/
def cregs : List Reg := .r1 :: yregs

theorem yr_cregs : ∀ k < 10, yr k ∈ cregs := by decide +kernel

theorem cregs_r2 : Reg.r2 ∉ cregs := by decide
theorem cregs_r12 : Reg.r12 ∉ cregs := by decide
theorem cregs_r0 : Reg.r0 ∉ cregs := by decide

theorem carryStep_ok {k : Nat} (hk : k < 9) {s : State} (hm : s.gpr .r2 = maskV)
    (hb : (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 < 2 ^ 32) :
    WP isa (.block (carryStep k)) s fun s' =>
      (s'.gpr (yr (k + 1))).toNat = (s.gpr (yr (k + 1))).toNat + (s.gpr (yr k)).toNat / 2 ^ 13 ∧
      (s'.gpr (yr k)).toNat = (s.gpr (yr k)).toNat % 2 ^ 13 ∧ Keeps [yr k, yr (k + 1)] s s' := by
  have hne : yr k ≠ yr (k + 1) := fun h => absurd (yr_inj _ (by omega) _ (by omega) h) (by omega)
  have h2 : yr k ≠ .r2 := (yr_ne k hk).2.2.1
  refine wp_add (op2_lsr (by omega)) fun s1 u1 => wp_and (op2_reg _ _) fun s2 u2 => WP.block_nil ?_
  refine ⟨?_, ?_, (u1.keeps (by simp)).trans (u2.keeps (by simp))⟩
  · rw [u2.other _ hne.symm, u1.gpr, toNat_add_lt (by rw [toNat_shr]; exact hb), toNat_shr]
  · rw [u2.gpr, u1.other _ hne, u1.other _ (Ne.symm (yr_ne' (k + 1) (by omega)).2.1), hm, toNat_and_mask]

/-- After the carries from columns `a`, …, `a + k - 1`. -/
structure CI (f : Nat → Nat) (a : Nat) (s₀ : State) (k : Nat) (s : State) : Prop where
  cols : Cols (carryN f a k) s
  keeps : Keeps cregs s₀ s

theorem carries_ok (a n : Nat) (hn : n + a ≤ 9) {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19)
    {s : State} (hc : Cols f s) (hm : s.gpr .r2 = maskV) :
    WP isa (.block ((List.range n).flatMap fun k => carryStep (k + a))) s fun s' =>
      Cols (carryN f a n) s' ∧ Keeps cregs s s' := by
  refine WP.mono (wp_range_flatMap (M := isa) (CI f a s) (fun k s' hk h => ?_) n (Nat.le_refl _) s
    ⟨hc, Keeps.refl _ _⟩) fun s' h => ⟨h.cols, h.keeps⟩
  have hm' : s'.gpr .r2 = maskV := by rw [h.keeps.gpr _ cregs_r2, hm]
  have hb := carryN_step_lt f a hf k (by omega)
  refine WP.mono (carryStep_ok (k := k + a) (by omega) hm' (by
    rw [h.cols _ (by omega), h.cols _ (by omega)]; exact hb)) fun s'' ⟨e1, e0, hk⟩ => ⟨?_, ?_⟩
  · intro j hj
    simp only [carryN, cstep]
    by_cases ej : j = k + a
    · subst ej; rw [iteT rfl, e0, h.cols _ hj]
    by_cases ej' : j = k + a + 1
    · subst ej'; rw [iteF ej, iteT rfl, e1, h.cols _ hj, h.cols _ (by omega)]
    · rw [iteF ej, iteF ej', hk.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun e => ej (yr_inj _ hj _ (by omega) e), fun e => ej' (yr_inj _ hj _ (by omega) e)⟩),
        h.cols _ hj]
  · exact h.keeps.trans (hk.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact yr_cregs _ (by omega))

end VG.Proof.Poly1305.Arm

end

/-!
# Poly1305 on 32-bit ARM: carrying all columns, the final reduction, and words

Untrusted: everything here is checked by Lean.
-/

open VG.PowLit

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

theorem Cols.keep {v : Nat → Nat} {s s' : State} (h : Cols v s) {ws : List Reg} (hk : Keeps ws s s')
    (hw : ∀ j < 10, yr j ∉ ws) : Cols v s' := fun j hj => by rw [hk.gpr _ (hw j hj)]; exact h j hj

theorem carryFold_ok {f : Nat → Nat} (hf : ∀ j < 10, f j < 2 ^ 32 - 2 ^ 19) {s : State} (hc : Cols f s) :
    WP isa (.block carryFold) s fun s' =>
      Cols (fold f) s' ∧ s'.gpr .r2 = maskV ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  rw [carryFold, List.cons_append, List.cons_append]
  refine wp_movw fun s1 u1 => ?_
  have hc1 : Cols f s1 := hc.keep (u1.keeps (List.mem_singleton_self _)) fun j hj => by
    simpa using (yr_ne' j hj).2.1
  rw [List.append_assoc]
  refine WP.append (carries_ok 0 9 (by omega) hf hc1 u1.gpr) fun s2 ⟨hc2, k2⟩ => ?_
  have hl := fun j (hj : j < 9) => carryN_lt f 0 9 j (by omega) (by omega)
  have hF9 := hc2 9 (by omega)
  have hF0 := hc2 0 (by omega)
  have hF1 := hc2 1 (by omega)
  simp only [yr] at hF9 hF0 hF1
  have hm2 : s2.gpr .r2 = maskV := by rw [k2.gpr _ cregs_r2, u1.gpr]; rfl
  simp only [List.cons_append, List.nil_append]
  refine wp_mov (op2_lsr (by omega)) fun s3 u3 => wp_and (op2_reg _ _) fun s4 u4 => ?_
  refine wp_add (op2_lsl (by omega)) fun s5 u5 => wp_add (op2_reg _ _) fun s6 u6 => ?_
  -- The values of `r12`, `r1` and `r3`.
  have hc9 : (s3.gpr .r12).toNat = carryN f 0 9 9 / 2 ^ 13 := by rw [u3.gpr, toNat_shr, hF9]
  have hc9' : carryN f 0 9 9 / 2 ^ 13 < 2 ^ 19 := by have := (s2.gpr .r1).isLt; omega
  have h12 : (s5.gpr .r12).toNat = 5 * (carryN f 0 9 9 / 2 ^ 13) := by
    rw [u5.gpr, u4.other _ (by decide), toNat_add_lt (by rw [toNat_shl]; omega), toNat_shl, hc9]
    omega
  have h1 : (s6.gpr .r1).toNat = carryN f 0 9 9 % 2 ^ 13 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.gpr, u3.other _ (by decide),
      u3.other _ (by decide), hm2, toNat_and_mask, hF9]
  have h3 : (s6.gpr .r3).toNat = carryN f 0 9 0 + 5 * (carryN f 0 9 9 / 2 ^ 13) := by
    have := hl 0 (by omega)
    rw [u6.gpr, u5.other _ (by decide), u4.other _ (by decide), u3.other _ (by decide),
      toNat_add_lt (by rw [h12, hF0]; omega), h12, hF0]
  have h4 : (s6.gpr .r4).toNat = carryN f 0 9 1 := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hF1]
  have hm6 : s6.gpr .r2 = maskV := by
    rw [u6.other _ (by decide), u5.other _ (by decide), u4.other _ (by decide),
      u3.other _ (by decide), hm2]
  have hk6 : Keeps (.r2 :: .r12 :: cregs) s s6 :=
    (u1.keeps (by simp)).trans ((k2.mono fun r hr => by simp [hr]).trans ((u3.keeps (by simp)).trans
      ((u4.keeps (by simp [cregs])).trans ((u5.keeps (by simp)).trans (u6.keeps (by simp [cregs, yregs]))))))
  refine WP.mono (carryStep_ok (k := 0) (by omega) hm6 (by
    simp only [yr, Nat.zero_add]; rw [h3, h4]; have := hl 1 (by omega); omega))
    fun s7 ⟨e1, e0, k7⟩ => ⟨fun j hj => ?_, ?_, hk6.trans (k7.mono fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp [yr, cregs, yregs])⟩
  · simp only [Nat.zero_add] at e1 e0
    rcases Nat.lt_or_ge j 2 with h | h
    · obtain rfl | rfl : j = 0 ∨ j = 1 := by omega
      · rw [e0, fold_0]; simp only [yr] at h3 ⊢; rw [h3]
      · rw [e1, fold_1]; simp only [yr] at h3 h4 ⊢; rw [h3, h4]
    have k26 : Keeps [.r12, .r1, .r3] s2 s6 :=
      (u3.keeps (by simp)).trans ((u4.keeps (by simp)).trans ((u5.keeps (by simp)).trans
        (u6.keeps (by simp))))
    rcases Nat.lt_or_ge j 9 with h' | h'
    · have hn : ∀ j < 9, 2 ≤ j → yr j ∉ [Reg.r12, .r1, .r3] ∧ yr j ∉ [yr 0, yr (0 + 1)] := by decide +kernel
      rw [k7.gpr _ (hn j h' h).2, k26.gpr _ (hn j h' h).1, fold_mid f h h']
      exact hc2 j hj
    · rw [show j = 9 by omega, k7.gpr _ (by decide), fold_9]; exact h1
  · rw [k7.gpr _ (by simp [yr]), hm6]

theorem plus5_ok {K : Nat → Nat} (hK : ∀ j < 10, K j ≤ 2 ^ 13) {s : State} (hc : Cols K s) :
    WP isa (.block plus5) s fun s' => (s'.gpr .r12).toNat = chainT K 9 ∧ Keeps [.r12] s s' := by
  rw [plus5]
  refine wp_add (op2_imm (by decide)) fun s1 u1 => ?_
  have h0 := hc 0 (by omega)
  have hK0 := hK 0 (by omega)
  simp only [yr] at h0
  refine WP.mono (wp_range_flatMap (M := isa)
    (fun k s' => (s'.gpr .r12).toNat = chainT K k ∧ Keeps [.r12] s1 s')
    (fun k s' hk ⟨h12, hk'⟩ => ?_) 9 (Nat.le_refl _) s1
    ⟨by rw [u1.gpr, toNat_add_lt (by rw [h0]; simp; omega), h0]; rfl, Keeps.refl _ _⟩)
    fun s' ⟨h, k⟩ => ⟨h, (u1.keeps (by simp)).trans k⟩
  have hy : (s'.gpr (yr (k + 1))).toNat = K (k + 1) := by
    rw [hk'.gpr _ (by have := (yr_ne' (k + 1) (by omega)).2.2; simpa using this),
      u1.other _ (yr_ne' (k + 1) (by omega)).2.2]
    exact hc (k + 1) (by omega)
  have hle := chainT_le K hK k (by omega)
  have hle' := hK (k + 1) (by omega)
  refine wp_add (op2_lsr (by omega)) fun s2 u2 => WP.block_nil ⟨?_, hk'.trans (u2.keeps (by simp))⟩
  rw [u2.gpr, toNat_add_lt (by rw [toNat_shr, hy, h12]; omega), toNat_shr, hy, h12]
  rfl

theorem addC_ok {s : State} {t k0 : Nat} (ht : (s.gpr .r12).toNat = t) (ht' : t < 2 ^ 20)
    (h3 : (s.gpr .r3).toNat = k0) (hk0 : k0 < 2 ^ 20) :
    WP isa (.block addC) s fun s' => (s'.gpr .r3).toNat = k0 + 5 * (t / 2 ^ 13) ∧
      Keeps [.r12, .r3] s s' := by
  rw [addC]
  refine wp_mov (op2_lsr (by omega)) fun s1 u1 => wp_add (op2_lsl (by omega)) fun s2 u2 => ?_
  refine wp_add (op2_reg _ _) fun s3 u3 => WP.block_nil ⟨?_, (u1.keeps (by simp)).trans
    ((u2.keeps (by simp)).trans (u3.keeps (by simp)))⟩
  have e1 : (s1.gpr .r12).toNat = t / 2 ^ 13 := by rw [u1.gpr, toNat_shr, ht]
  have e2 : (s2.gpr .r12).toNat = 5 * (t / 2 ^ 13) := by
    rw [u2.gpr, toNat_add_lt (by rw [toNat_shl, e1]; omega), toNat_shl, e1]; omega
  rw [u3.gpr, u2.other _ (by decide), u1.other _ (by decide),
    toNat_add_lt (by rw [h3, e2]; omega), h3, e2]

theorem reduceRegs_ok {E : Nat → Nat} (hE : ∀ j < 10, E j < 2 ^ 32 - 2 ^ 19) {s : State}
    (hc : Cols E s) :
    WP isa (.block reduceRegs) s fun s' =>
      Cols (redL E) s' ∧ s'.gpr .r2 = maskV ∧ Keeps (.r2 :: .r12 :: cregs) s s' := by
  obtain ⟨hH, hK, hK', -, -⟩ := red_facts E hE
  rw [reduceRegs]
  simp only [List.append_assoc]
  refine WP.append (carryFold_ok hE hc) fun s1 ⟨hc1, hm1, k1⟩ => ?_
  refine WP.append (carries_ok 1 8 (by omega) hH hc1 hm1) fun s2 ⟨hc2, k2⟩ => ?_
  refine WP.append (plus5_ok hK hc2) fun s3 ⟨h12, k3⟩ => ?_
  have hc3 : Cols (redK E) s3 := hc2.keep k3 fun j hj => by simpa using (yr_ne' j hj).2.2
  have ht : chainT (redK E) 9 < 2 ^ 20 := by have := chainT_le _ hK 9 (by omega); omega
  have h30 : (s3.gpr .r3).toNat = redK E 0 := hc3 0 (by omega)
  have hk0 := hK 0 (by omega)
  refine WP.append (addC_ok h12 ht h30 (by omega)) fun s4 ⟨h4, k4⟩ => ?_
  have hc4 : Cols (redK' E) s4 := fun j hj => by
    simp only [redK']
    split
    · rename_i e; subst e; show (s4.gpr .r3).toNat = _; rw [h4, chainT_top]; rfl
    · rw [k4.gpr _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨(yr_ne' j hj).2.2, fun e => by have := yr_inj _ hj 0 (by omega) e; omega⟩)]
      exact hc3 j hj
  have hm4 : s4.gpr .r2 = maskV := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ cregs_r2, hm1]
  rw [carry3]
  refine WP.append (carries_ok 0 9 (by omega) hK' hc4 hm4) fun s5 ⟨hc5, k5⟩ => ?_
  have hm5 : s5.gpr .r2 = maskV := by rw [k5.gpr _ cregs_r2, hm4]
  refine wp_and (op2_reg _ _) fun s6 u6 => WP.block_nil ⟨fun j hj => ?_, ?_, ?_⟩
  · simp only [redL]
    split
    · rename_i e; subst e
      have := hc5 9 (by omega)
      simp only [yr] at this ⊢
      rw [u6.gpr, hm5, toNat_and_mask, this]
    · rw [u6.other _ (fun e => by have := yr_inj _ hj 9 (by omega) e; omega)]
      exact hc5 j hj
  · rw [u6.other _ (by decide), hm5]
  · refine k1.trans ((k2.mono fun r hr => by simp [hr]).trans ((k3.mono (by simp)).trans
      ((k4.mono (by simp [cregs, yregs])).trans ((k5.mono fun r hr => by simp [hr]).trans
        (u6.keeps (by simp [cregs]))))))

/-- The words of the limbs `L` (see `val_toWords`). -/
def tw0 (L : Nat → Nat) : Nat := L 0 + 2 ^ 13 * L 1 + 2 ^ 26 * (L 2 % 2 ^ 6)
def tw1 (L : Nat → Nat) : Nat := L 2 / 2 ^ 6 + 2 ^ 7 * L 3 + 2 ^ 20 * (L 4 % 2 ^ 12)
def tw2 (L : Nat → Nat) : Nat := L 4 / 2 ^ 12 + 2 * L 5 + 2 ^ 14 * L 6 + 2 ^ 27 * (L 7 % 2 ^ 5)
def tw3 (L : Nat → Nat) : Nat := L 7 / 2 ^ 5 + 2 ^ 8 * L 8 + 2 ^ 21 * (L 9 % 2 ^ 11)

theorem add_shl {x y : BitVec 32} {a : Nat} (h : x.toNat + y.toNat * 2 ^ a % 2 ^ 32 < 2 ^ 32) :
    (x + y <<< a).toNat = x.toNat + y.toNat * 2 ^ a % 2 ^ 32 := by
  rw [toNat_add_lt (by rw [toNat_shl]; exact h), toNat_shl]

theorem toWords_ok {L : Nat → Nat} {s : State} (hc : Cols L s) (hL : ∀ j < 9, L j < 2 ^ 13) :
    WP isa (.block toWords) s fun s' =>
      (s'.gpr .r3).toNat = tw0 L ∧ (s'.gpr .r5).toNat = tw1 L ∧ (s'.gpr .r7).toNat = tw2 L ∧
      (s'.gpr .r10).toNat = tw3 L ∧ (s'.gpr .r1).toNat = L 9 / 2 ^ 11 ∧
      Keeps [.r1, .r3, .r5, .r7, .r10] s s' := by
  have c0 := hc 0 (by omega); have c1 := hc 1 (by omega); have c2 := hc 2 (by omega)
  have c3 := hc 3 (by omega); have c4 := hc 4 (by omega); have c5 := hc 5 (by omega)
  have c6 := hc 6 (by omega); have c7 := hc 7 (by omega); have c8 := hc 8 (by omega)
  have c9 := hc 9 (by omega)
  simp only [yr] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  have l0 := hL 0 (by omega); have l1 := hL 1 (by omega); have l2 := hL 2 (by omega)
  have l3 := hL 3 (by omega); have l4 := hL 4 (by omega); have l5 := hL 5 (by omega)
  have l6 := hL 6 (by omega); have l7 := hL 7 (by omega); have l8 := hL 8 (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [toWords, runBlock_cons, runStep_some, runBlock_nil, exec,
    Op2.eval, isa, State.setReg, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [add_shl (by rw [add_shl (by omega)]; omega), add_shl (by omega), c0, c1, c2, tw0]; omega
  · rw [add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr, c2, c3, c4, tw1]; omega
  · rw [add_shl (by rw [add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr, c4, c5, c6, c7, tw2]; omega
  · rw [add_shl (by rw [add_shl (by rw [toNat_shr]; omega), toNat_shr]; omega),
      add_shl (by rw [toNat_shr]; omega), toNat_shr, c7, c8, c9, tw3]; omega
  · rw [toNat_shr, c9]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h3, h5, h7, h10⟩ := hr
    simp [h1, h3, h5, h7, h10]

end VG.Proof.Poly1305.Arm
