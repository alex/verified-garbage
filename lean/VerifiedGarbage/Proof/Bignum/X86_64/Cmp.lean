import VerifiedGarbage.Proof.Bignum.X86_64.Csub

/-!
# Multiword arithmetic on x86-64: comparison

`X - m` over `w` words, with the borrow kept in `rbp` as a mask and the
difference discarded: `rbp` ends as the mask of `X < m` (`cmpLoop_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The comparison loop's body. -/
abbrev cmpBody : List Instr :=
  [cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)), cfToRbp]

/-- After `j` words from `s₀`: the low `j` words `X_j` and `m_j` and the
borrow `c` of `X_j - m_j`. -/
structure CmpInv (s₀ : State) (B : Addr) (Z eX eN : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  mem : t.mem = s₀.mem
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  val : ∃ (c : Bool) (d : Nat), t.gpr .rbp = mask c ∧ d < 2 ^ (64 * j) ∧
    d + wv s₀.mem B eN j = wv s₀.mem B eX j + 2 ^ (64 * j) * c.toNat

theorem cmpStep_ok {s₀ : State} {B : Addr} {Z w eX eN : Nat}
    (hbx : s₀.gpr .rbx = off B eX) (h10 : s₀.gpr .r10 = off B eN)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    {j : Nat} (hj : j < w) {t : State} (hI : CmpInv s₀ B Z eX eN j t) :
    WP isa (.block (cmpBody ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ CmpInv s₀ B Z eX eN (j + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B eX := (hI.keep.gpr (by decide)).trans hbx
  have t10 : t.gpr .r10 = off B eN := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, d, hbp, hd, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ => t₁.mem = t.mem ∧
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64,
        r.toNat + (word t.mem B (eN + 8 * j)).toNat + c.toNat =
          (word t.mem B (eX + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl)
    fun t₁ ⟨⟨hm, c', h₁, r, hr⟩, k₁⟩ => ?_
  · unfold cmpBody cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 tbx hI.r14, addr0 t10 hI.r14, hbp, cf_mask,
      hI.scr.ld (show eX + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  rw [hI.mem] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide),
    by rw [hm', hm, hI.mem], h14, ⟨c', d + 2 ^ (64 * j) * r.toNat, (k'.gpr (by decide)).trans h₁, ?_, ?_⟩⟩
  · have := Nat.mul_le_mul_left (2 ^ (64 * j)) (show r.toNat + 1 ≤ 2 ^ 64 from r.isLt)
    rw [pow64_succ]; rw [Nat.mul_add, Nat.mul_one] at this; omega
  · simp only [wv]
    rw [pow64_succ]
    zify at hr hval ⊢
    linear_combination hval + (2 ^ (64 * j) : ℤ) * hr

theorem lt_of_borrow {X N d P : Nat} {c : Bool} (hd : d < P)
    (h : d + N = X + P * c.toNat) : c = decide (X < N) := by
  cases c <;> simp only [Bool.toNat_true, Bool.toNat_false, Nat.mul_one, Nat.mul_zero] at h <;>
    (symm; simp only [decide_eq_true_eq, decide_eq_false_iff_not]) <;> omega

/-- `rbp := 0`, then the loop: `rbp` the mask of `X < m` for the `w`-word
numbers at `rbx` and `r10`. -/
theorem cmpLoop_ok {s : State} {B : Addr} {Z w eX eN : Nat} (hs : Scr s B Z)
    (hbx : s.gpr .rbx = off B eX) (h10 : s.gpr .r10 = off B eN)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hbp : s.gpr .rbp = mask false) (hw : 1 ≤ w) (hw' : w < 2 ^ 31)
    (hX : eX + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z) :
    WP isa (wordLoop 0 cmpBody) s fun t =>
      t.gpr .rbp = mask (decide (wv s.mem B eX w < wv s.mem B eN w)) ∧ t.mem = s.mem ∧
      Keep [.rax, .rbp, .r14] s t := by
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      CmpInv s B Z eX eN 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), hm, h14,
      ⟨false, 0, (k.gpr (by decide)).trans hbp, Nat.one_pos, rfl⟩⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (CmpInv s B Z eX eN) h0
    (fun j _ hj t hI => cmpStep_ok hbx h10 h12 (by omega) hX hN hj hI)) fun t hI => ?_
  obtain ⟨c, d, hc, hd, hval⟩ := hI.val
  exact ⟨by rw [hc, lt_of_borrow hd hval], hI.mem, hI.keep⟩

end VG.Proof.Bignum.X86_64
