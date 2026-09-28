import VerifiedGarbage.Proof.Poly1305.Arm.Common

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

theorem yr_yregs : ∀ k < 9, yr k ∈ yregs := by decide

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
  refine WP.mono (wp_range_flatMap (M := isa) (WI s₀) (addWord_step hin) 4 le_rfl s₀
    ⟨fun j _ => by simp [wsum], fun h => absurd h (by omega), Keeps.refl _ _⟩)
    fun s h => ⟨h.cols, h.r2 (by omega), h.keeps⟩

/-! ## The limbs as numbers -/

/-- The limbs `addWords` adds, as numbers. -/
theorem wsum_toNat (w : Nat → BitVec 32) {k : Nat} (hk : k < 9) :
    (wsum w 4 k).toNat = mlimb (w 0).toNat (w 1).toNat (w 2).toNat (w 3).toNat k := by
  have h0 := (w 0).isLt; have h1 := (w 1).isLt; have h2 := (w 2).isLt; have h3 := (w 3).isLt
  interval_cases k <;>
  simp only [wsum, contrib, pieces, pieceBV, mlimb, Nat.reduceEqDiff, ite_true, ite_false,
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
