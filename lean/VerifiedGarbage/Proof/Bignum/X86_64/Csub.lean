import VerifiedGarbage.Proof.Bignum.X86_64.Rounds

/-!
# Multiword arithmetic on x86-64: the conditional subtraction

`subMod` computes `T - m` into the temporary array (`rsi`) over `w` words,
with the borrow between iterations kept in `rbp` as a mask (`mask`), and
then the borrow of `T - m` with the top word of `T` counted: `rbp` all
ones iff `T < m` (`subMod_ok`). `selectAcc` then stores `T` or `T - m` by
the mask (`selectAcc_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- The mask of a borrow, as `sbb rbp, rbp` leaves it. -/
def mask (c : Bool) : BitVec 64 := 0 - (BitVec.ofBool c).setWidth 64

theorem mask_false : mask false = 0 := rfl
theorem mask_true : mask true = BitVec.allOnes 64 := rfl

/-- `add rbp, rbp` sets the carry from the mask. -/
theorem cf_mask (c : Bool) : decide (2 ^ 64 ≤ (mask c).toNat + (mask c).toNat) = c := by
  cases c <;> decide

/-- `sbb`, as numbers: `a - b - c`, plus `2⁶⁴` if it borrows. -/
theorem sbb_toNat (a b : BitVec 64) (c : Bool) :
    (a - b - (BitVec.ofBool c).setWidth 64).toNat + b.toNat + c.toNat =
      a.toNat + 2 ^ 64 * (decide (a.toNat < b.toNat + c.toNat)).toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_sub, BitVec.toNat_sub, hc]
  by_cases h : a.toNat < b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- The selection: `((a ^ b) & m) ^ b` is `a` for the mask of `true`, `b`
for that of `false`. -/
theorem select_mask (a b : BitVec 64) (c : Bool) :
    ((a ^^^ b) &&& mask c) ^^^ b = if c then a else b := by
  cases c
  · simp [mask_false]
  · simp only [mask_true, BitVec.and_allOnes, ite_true]
    rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-! ## `T - m` -/

/-- After `j` words of `subMod`'s loop from `s₀`: `D_j + m_j = T_j + 2^(64 j) c`
for the low `j` words `D_j` of the difference, `m_j` of `m`, `T_j` of `T`,
and the borrow `c` (as `mask c` in `rbp`). -/
structure SubInv (s₀ : State) (B : Addr) (Z eA eN eT : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eT (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eT j + wv s₀.mem B eN j = wv s₀.mem B eA j + 2 ^ (64 * j) * c.toNat

theorem subStep_ok {s₀ : State} {B : Addr} {Z w eA eN eT : Nat}
    (h8 : s₀.gpr .r8 = off B eA) (h10 : s₀.gpr .r10 = off B eN) (hsi : s₀.gpr .rsi = off B eT)
    (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w) (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z)
    (hN : eN + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sA : eT + 8 * w ≤ eA ∨ eA + 8 * w ≤ eT) (sN : eT + 8 * w ≤ eN ∨ eN + 8 * w ≤ eT)
    {j : Nat} (hj : j < w) {t : State} (hI : SubInv s₀ B Z eA eN eT j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .r8 .r14)), .alu .sbb .rax (.mem (ix .r10 .r14)),
        .store (ix .rsi .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ SubInv s₀ B Z eA eN eT (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t10 : t.gpr .r10 = off B eN := (hI.keep.gpr (by decide)).trans h10
  have tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eT + 8 * j)) r ∧
        r.toNat + (word t.mem B (eN + 8 * j)).toNat + c.toNat =
          (word t.mem B (eA + 8 * j)).toNat + 2 ^ 64 * c'.toNat) ?_ rfl) fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 t8 hI.r14, addr0 t10 hI.r14, addr0 tsi hI.r14, hbp, cf_mask,
      hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eN + 8 * j + 8 ≤ Z by omega),
      hI.scr.st (show eT + 8 * j + 8 ≤ Z by omega)]
    exact ⟨_, rfl, _, rfl, sbb_toNat _ _ _⟩
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eA + 8 * j) = word s₀.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eN + 8 * j) = word s₀.mem B (eN + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx, hy] at hr
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_,
    ⟨c', (k'.gpr (by decide)).trans h₁, ?_⟩⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B r (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega)]
    simp only [wv]
    rw [pow64_succ]
    zify at hr hval ⊢
    linear_combination hval + (2 ^ (64 * j) : ℤ) * hr

/-- `subMod`: `D = T - m` over `w` words into the array at `rsi`, its borrow
`c`, and `rbp` the mask of `T_w < c` for the word `w` of `T` (that is, of
`T < m` when `T < 2 · 2^(64 w)`). -/
theorem subMod_ok {s : State} {B : Addr} {Z w eA eN eT : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h10 : s.gpr .r10 = off B eN) (hsi : s.gpr .rsi = off B eT)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 1) ≤ Z)
    (hN : eN + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z)
    (sA : eT + 8 * w ≤ eA ∨ eA + 8 * (w + 1) ≤ eT) (sN : eT + 8 * w ≤ eN ∨ eN + 8 * w ≤ eT) :
    WP isa subMod s fun t => ∃ c lt : Bool, t.gpr .rbp = mask lt ∧
      lt = decide ((word s.mem B (eA + 8 * w)).toNat < c.toNat) ∧
      wv t.mem B eT w + wv s.mem B eN w = wv s.mem B eA w + 2 ^ (64 * w) * c.toNat ∧
      Outside B eT (8 * w) s.mem t.mem ∧ Keep [.rax, .rbp, .r14] s t := by
  have hn := hs.nowrap
  unfold subMod
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = mask false ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hbp, hm₁⟩, k₁⟩ => ?_)
  have s₁8 : s₁.gpr .r8 = off B eA := (k₁.gpr (by decide)).trans h8
  have s₁10 : s₁.gpr .r10 = off B eN := (k₁.gpr (by decide)).trans h10
  have s₁si : s₁.gpr .rsi = off B eT := (k₁.gpr (by decide)).trans hsi
  have s₁12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      SubInv s₁ B Z eA eN eT 0 t := fun t h14 hm k _ =>
    ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (SubInv s₁ B Z eA eN eT) h0
    (fun j _ hj t hI => subStep_ok s₁8 s₁10 s₁si s₁12 (by omega) (by omega) hN hT (by omega) sN hj hI))
    fun t hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans s₁8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans s₁12
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (by omega) (by omega), hm₁]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t' => t'.mem = t.mem ∧
      t'.gpr .rbp = mask (decide ((word s.mem B (eA + 8 * w)).toNat < c.toNat)))
    (by
      unfold cfFromRbp cfToRbp
      xrun [State.ea, ix, addr0 t8 t12, hc, cf_mask, hI.scr.ld (show eA + 8 * w + 8 ≤ Z by omega), hX, sx0]
      simp only [show (0 : BitVec 64).toNat = 0 from rfl, Nat.zero_add]
      rfl) rfl) fun t' ⟨⟨hm', hbp'⟩, k'⟩ => ?_
  refine ⟨c, _, hbp', rfl, ?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', ← hm₁]; exact hval
  · rw [hm', ← hm₁]; exact hI.out

/-! ## The selection -/

structure SelInv (s₀ : State) (B : Addr) (Z eA eT eo : Nat) (lt : Bool) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eo (8 * j) s₀.mem t.mem
  val : wv t.mem B eo j = if lt then wv s₀.mem B eA j else wv s₀.mem B eT j

theorem selectAcc_ok {s : State} {B : Addr} {Z w eA eT eo : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (hsi : s.gpr .rsi = off B eT) (hbx : s.gpr .rbx = off B eo)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) {lt : Bool} (hbp : s.gpr .rbp = mask lt)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * w ≤ Z) (hT : eT + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) (sT : eo + 8 * w ≤ eT ∨ eT + 8 * w ≤ eo) :
    WP isa selectAcc s fun t =>
      wv t.mem B eo w = (if lt then wv s.mem B eA w else wv s.mem B eT w) ∧
      Outside B eo (8 * w) s.mem t.mem ∧ Keep [.rax, .rdx, .r14] s t := by
  have hn := hs.nowrap
  unfold selectAcc
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s.mem → Keep [.r14] s t → t.cf = s.cf →
      SelInv s B Z eA eT eo lt 0 t := fun t h14 hm k _ =>
    ⟨hs.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, by
      cases lt <;> rfl⟩
  refine WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw' (SelInv s B Z eA eT eo lt) h0 ?_)
    fun t hI => ⟨hI.val, hI.out, hI.keep⟩
  intro j _ hj t hI
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tsi : t.gpr .rsi = off B eT := (hI.keep.gpr (by decide)).trans hsi
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tbp : t.gpr .rbp = mask lt := (hI.keep.gpr (by decide)).trans hbp
  have hx : word t.mem B (eA + 8 * j) = word s.mem B (eA + 8 * j) := hI.out.word (by omega) (by omega)
  have hy : word t.mem B (eT + 8 * j) = word s.mem B (eT + 8 * j) := hI.out.word (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (eo + 8 * j))
      (if lt then word s.mem B (eA + 8 * j) else word s.mem B (eT + 8 * j))) (by
      xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tsi hI.r14, addr0 tbx hI.r14, tbp,
        hI.scr.ld (show eA + 8 * j + 8 ≤ Z by omega), hI.scr.ld (show eT + 8 * j + 8 ≤ Z by omega),
        hI.scr.st (show eo + 8 * j + 8 ≤ Z by omega), hx, hy, select_mask]) rfl) fun t₁ ⟨hm, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), ((hI.keep.trans k₁).trans k').mono (by decide), h14, ?_, ?_⟩
  · rw [hm', hm]
    intro x hx'
    rw [writeW_outside t.mem B _ (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hm', hm, wv_writeW_top _ _ _ _ _ (by omega), hI.val]
    cases lt <;> simp [wv]

end VG.Proof.Bignum.X86_64
