import VerifiedGarbage.Proof.Bignum.X86_64.Store
import Mathlib.Data.Int.ModEq

/-!
# Multiword arithmetic on x86-64: setting up

`minv`: `-m₀⁻¹ mod 2⁶⁴` for an odd `m₀` (`minv_ok`), by five steps of
Newton's iteration from `x = m₀`, which is right modulo 8.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64
open VG.Proof.Bignum (newton_step emod_pow_weaken odd_sq)

theorem toNat_ofNat_modEq (n : Nat) : ((BitVec.ofNat 64 n).toNat : Int) ≡ n [ZMOD 2 ^ 64] := by
  rw [BitVec.toNat_ofNat]; push_cast; exact Int.mod_modEq _ _

theorem toNat_two_sub_modEq (y : BitVec 64) :
    ((BitVec.setWidth 64 (2 : BitVec 32) - y).toNat : Int) ≡ 2 - y.toNat [ZMOD 2 ^ 64] := by
  rw [BitVec.toNat_sub, show (BitVec.setWidth 64 (2 : BitVec 32)).toNat = 2 from rfl]
  have hy := y.isLt
  have : ((2 ^ 64 - y.toNat + 2 : Nat) : Int) = 2 - y.toNat + 2 ^ 64 := by push_cast [Nat.cast_sub hy.le]; ring
  rw [Int.natCast_emod, this]
  refine (Int.mod_modEq _ _).trans ?_
  show (2 - (y.toNat : Int) + 2 ^ 64) % 2 ^ 64 = (2 - (y.toNat : Int)) % 2 ^ 64
  exact Int.add_emod_right _ _

/-- The value of a Newton step, modulo `2⁶⁴`. -/
theorem newton_val (a x : BitVec 64) :
    ((BitVec.ofNat 64 (x.toNat * (BitVec.setWidth 64 (2 : BitVec 32) -
      BitVec.ofNat 64 (a.toNat * x.toNat)).toNat)).toNat : Int) ≡
      x.toNat * (2 - a.toNat * x.toNat) [ZMOD 2 ^ 64] := by
  refine (toNat_ofNat_modEq _).trans ?_
  push_cast
  refine Int.ModEq.mul_left _ ((toNat_two_sub_modEq _).trans (Int.ModEq.sub_left 2 ?_))
  exact toNat_ofNat_modEq _

theorem newton_ok (t : State) :
    WP isa (.block newton) t fun t' =>
      (((t'.gpr .rcx).toNat : Int) - (t.gpr .rcx).toNat * (2 - (t.gpr .rbx).toNat * (t.gpr .rcx).toNat)) %
        (2 ^ 64 : Int) = 0 ∧ t'.gpr .rbx = t.gpr .rbx ∧ t'.mem = t.mem ∧ Keep [.rax, .rcx, .rdx, .rsi] t t' := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rsi] (c := .block newton) (Q := fun t' =>
    (((t'.gpr .rcx).toNat : Int) - (t.gpr .rcx).toNat * (2 - (t.gpr .rbx).toNat * (t.gpr .rcx).toNat)) %
        (2 ^ 64 : Int) = 0 ∧ t'.gpr .rbx = t.gpr .rbx ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold newton
  xrun
  exact Int.emod_eq_zero_of_dvd (newton_val _ _).symm.dvd

/-- A Newton step on the state: `a x' ≡ 1 (mod 2^(2j))` from `a x ≡ 1 (mod 2^j)`. -/
theorem newton_step_ok (t : State) {j : Nat} (hj : 2 * j ≤ 64)
    (h : (((t.gpr .rbx).toNat : Int) * (t.gpr .rcx).toNat - 1) % (2 ^ j : Int) = 0) :
    WP isa (.block newton) t fun t' =>
      (((t'.gpr .rbx).toNat : Int) * (t'.gpr .rcx).toNat - 1) % (2 ^ (2 * j) : Int) = 0 ∧
      t'.gpr .rbx = t.gpr .rbx ∧ t'.mem = t.mem ∧ Keep [.rax, .rcx, .rdx, .rsi] t t' :=
  WP.mono (newton_ok t) fun t' ⟨hv, hb, hm, k⟩ => ⟨by rw [hb]; exact newton_step hj h hv, hb, hm, k⟩

/-- Negating an inverse: `a (-x) + 1 ≡ 0` from `a x ≡ 1 (mod 2⁶⁴)`. -/
theorem neg_inv {a x : Nat} (hx : x < 2 ^ 64) (h : ((a : Int) * x - 1) % (2 ^ 64 : Int) = 0) :
    (a * ((2 ^ 64 - x + 0) % 2 ^ 64) + 1) % 2 ^ 64 = 0 := by
  have hr : (((2 ^ 64 - x + 0) % 2 ^ 64 : Nat) : Int) ≡ -(x : Int) [ZMOD 2 ^ 64] := by
    rw [Int.natCast_emod]
    refine (Int.mod_modEq _ _).trans ?_
    unfold Int.ModEq
    omega
  have h2 : ((a * ((2 ^ 64 - x + 0) % 2 ^ 64) + 1 : Nat) : Int) ≡ -((a : Int) * x - 1) [ZMOD 2 ^ 64] := by
    push_cast
    have := (hr.mul_left (a : Int)).add_right 1
    refine this.trans ?_
    rw [show (a : Int) * -(x : Int) + 1 = -((a : Int) * x - 1) by ring]
  have h3 : -((a : Int) * x - 1) ≡ 0 [ZMOD 2 ^ 64] := by
    unfold Int.ModEq
    rw [Int.emod_eq_zero_of_dvd (dvd_neg.mpr (Int.dvd_of_emod_eq_zero h))]
    rfl
  have h4 := h2.trans h3
  exact_mod_cast h4

/-- `minv`: `-m₀⁻¹ mod 2⁶⁴` into `r15`, for the odd `m₀` in `rbx`. -/
theorem minv_ok (s : State) (hodd : (s.gpr .rbx).toNat % 2 = 1) :
    WP isa (.block minv) s fun t =>
      ((s.gpr .rbx).toNat * (t.gpr .r15).toNat + 1) % 2 ^ 64 = 0 ∧
      Keep [.rax, .rcx, .rdx, .rsi, .r15] s t ∧ t.mem = s.mem := by
  unfold minv
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rcx] (c := .block [.mov .rcx (.reg .rbx)]) (Q := fun t =>
    t.gpr .rcx = s.gpr .rbx ∧ t.mem = s.mem) (by xrun) rfl) fun t₀ ⟨⟨h₀, hm₀⟩, k₀⟩ => ?_
  have hb₀ : t₀.gpr .rbx = s.gpr .rbx := k₀.gpr (by decide)
  have e₀ : (((t₀.gpr .rbx).toNat : Int) * (t₀.gpr .rcx).toNat - 1) % (2 ^ 3 : Int) = 0 := by
    rw [hb₀, h₀]
    have h1 := odd_sq _ hodd
    have h2 : (((s.gpr .rbx).toNat : Int) * (s.gpr .rbx).toNat) % 8 = 1 := by exact_mod_cast h1
    show (((s.gpr .rbx).toNat : Int) * (s.gpr .rbx).toNat - 1) % 8 = 0
    omega
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₀ (j := 3) (by norm_num) e₀) fun t₁ ⟨e₁, hb₁, hm₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₁ (j := 6) (by norm_num) e₁) fun t₂ ⟨e₂, hb₂, hm₂, k₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₂ (j := 12) (by norm_num) e₂) fun t₃ ⟨e₃, hb₃, hm₃, k₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₃ (j := 24) (by norm_num) e₃) fun t₄ ⟨e₄, hb₄, hm₄, k₄⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (newton_step_ok t₄ (j := 32) (by norm_num) (emod_pow_weaken (by norm_num) e₄))
    fun t₅ ⟨e₅, hb₅, hm₅, k₅⟩ => ?_
  have hb : t₅.gpr .rbx = s.gpr .rbx := hb₅.trans (hb₄.trans (hb₃.trans (hb₂.trans (hb₁.trans hb₀))))
  have kk := ((((k₀.trans k₁).trans k₂).trans k₃).trans k₄).trans k₅
  rw [hb] at e₅
  refine WP.mono (WP.keep [.r15] (Q := fun t => t.gpr .r15 = 0 - t₅.gpr .rcx ∧ t.mem = t₅.mem)
    (by xrun; rfl) rfl) fun t ⟨⟨h15, hm⟩, k⟩ => ⟨?_, (kk.trans k).mono (by decide), ?_⟩
  · rw [h15, BitVec.toNat_sub, show (0 : BitVec 64).toNat = 0 from rfl]
    exact neg_inv (t₅.gpr .rcx).isLt e₅
  · rw [hm, hm₅, hm₄, hm₃, hm₂, hm₁, hm₀]

/-! ## The arrays' bases -/

theorem setBase_ok {t : State} {B : Addr} {Z w j : Nat} (hs : Scr t B Z) (hdi : t.gpr .rdi = B)
    (hj : j < 8) (hZ : 8 * sArr 8 ≤ Z) (hdx : t.gpr .rdx = off B (slot w j))
    (hax : t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block (setBase j)) t fun t' =>
      t'.mem = t.mem.writeW (off B (8 * sArr j)) (off B (slot w j)) ∧
      t'.gpr .rdx = off B (slot w (j + 1)) ∧ Keep [.rdx] t t' := by
  have h8 : 8 * sArr j + 8 ≤ 8 * sArr 8 := by unfold sArr; omega
  have hst : InRegions t.wr (off B (8 * sArr j)) 8 := hs.st (by omega)
  refine WP.mono (WP.keep [.rdx] (c := .block (setBase j)) (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (8 * sArr j)) (off B (slot w j)) ∧
      t'.gpr .rdx = off B (slot w (j + 1))) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold setBase
  xrun [State.ea, hdr, hdi, hdrOff, hst, hdx, hax]
  rw [off, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  unfold slot; rw [Nat.add_mul, Nat.one_mul]; omega

theorem setBasesN_ok {B : Addr} {Z w : Nat} (hZ : 8 * sArr 8 ≤ Z) :
    ∀ n ≤ 8, ∀ t : State, Scr t B Z → t.gpr .rdi = B → t.gpr .rdx = off B (slot w 0) →
      t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2)) →
      WP isa (.block ((List.range n).flatMap setBase)) t fun t' =>
        (∀ j < n, word t'.mem B (8 * sArr j) = off B (slot w j)) ∧ t'.gpr .rdx = off B (slot w n) ∧
        Outside B (8 * sArr 0) (8 * n) t.mem t'.mem ∧ Keep [.rdx] t t' := by
  intro n
  induction n with
  | zero =>
    intro _ t _ _ hdx _
    exact WP.block_nil ⟨fun j hj => absurd hj (by omega), hdx, Outside.refl _ _ _ _, Keep.refl _ _⟩
  | succ n ih =>
    intro hn t hs hdi hdx hax
    have hnZ := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (ih (by omega) t hs hdi hdx hax) fun t₁ ⟨hw₁, hdx₁, ho₁, k₁⟩ => ?_
    refine WP.mono (setBase_ok (hs.congr k₁.2.2) ((k₁.gpr (by decide)).trans hdi) (by omega) hZ hdx₁
      ((k₁.gpr (by decide)).trans hax)) fun t' ⟨hm, hdx', k'⟩ => ⟨?_, hdx', ?_, k₁.trans k' |>.mono (by decide)⟩
    · intro j hj
      rw [hm]
      by_cases hjn : j = n
      · subst hjn; exact word_writeW_self _ _ _ _
      · rw [(writeW_outside t₁.mem B _ (by unfold sArr at *; omega)).word
          (by unfold sArr; omega) (by unfold sArr; omega)]
        exact hw₁ j (by omega)
    · rw [hm]
      intro x hx
      rw [writeW_outside t₁.mem B _ (by unfold sArr; omega) x (by unfold sArr at *; omega)]
      exact ho₁ x (by omega)

/-- `setBases`: the arrays' bases into the header, for `w` in `r12`. -/
theorem setBases_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (hZ : 8 * sArr 8 ≤ Z) :
    WP isa (.block setBases) s fun t =>
      (∀ j < 8, word t.mem B (8 * sArr j) = off B (slot w j)) ∧
      Outside B (8 * sArr 0) 64 s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  unfold setBases
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 (8 * (w + 2)) ∧
      t.gpr .rdx = off B (slot w 0) ∧ t.mem = s.mem) ?_ rfl) fun t ⟨⟨hax, hdx, hm⟩, k⟩ => ?_
  · xrun [h12, hdi, sx_ofNat (show hdrBytes < 2 ^ 31 by decide)]
    refine ⟨?_, by simp [off, slot]⟩
    rw [show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl]
    simp only [← BitVec.ofNat_add]
    congr 1; omega
  refine WP.mono (setBasesN_ok hZ 8 (by omega) t (hs.congr k.2.2) ((k.gpr (by decide)).trans hdi) hdx hax)
    fun t' ⟨hw', _, ho, k'⟩ => ⟨hw', by rw [← hm]; exact ho, (k.trans k').mono (by decide)⟩

end VG.Proof.Bignum.X86_64
