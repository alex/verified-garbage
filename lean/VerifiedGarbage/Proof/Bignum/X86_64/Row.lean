import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Multiword arithmetic on x86-64: `acc += a_i B`

`mulAddRow` adds `rcx · B` (the `w` words at `r9`) into the accumulator
(the `w + 2` words at `r8`): a loop of multiply-accumulate steps over the
`w` words of `B`, then the last carry into words `w` and `w + 1`
(`mulAddRow_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `b + 8 i + 0` for `b = p + e`, `i = j`, as `xrun` leaves it. -/
theorem addr0 {b i p : Addr} {e j : Nat} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 0 = off p (e + 8 * j) := by
  subst hb hi
  rw [ofNat_mul8, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero, off, BitVec.add_assoc,
    ← BitVec.ofNat_add]

/-- `b + 8 i - 8` for `i = j ≥ 1`. -/
theorem addrm8 {b i p : Addr} {e j : Nat} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j) (hj : 1 ≤ j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 (-8) = off p (e + 8 * (j - 1)) := by
  have h8 : BitVec.ofNat 64 (8 * j) + BitVec.ofInt 64 (-8) = BitVec.ofNat 64 (8 * (j - 1)) := by
    rw [show (-8 : Int) = - ((8 : Nat) : Int) by rfl, BitVec.ofInt_neg, BitVec.ofInt_natCast,
      ← BitVec.sub_eq_add_neg, show 8 * j = 8 * (j - 1) + 8 by omega, BitVec.ofNat_add,
      BitVec.add_sub_cancel]
  subst hb hi
  rw [ofNat_mul8, off, BitVec.add_assoc, BitVec.add_assoc, h8, ← BitVec.ofNat_add]

/-- `b + 8 i + 8`. -/
theorem addr8 {b i p : Addr} {e j : Nat} (hb : b = off p e) (hi : i = BitVec.ofNat 64 j) :
    b + i * BitVec.ofNat 64 8 + BitVec.ofInt 64 8 = off p (e + 8 * j + 8) := by
  subst hb hi
  rw [ofNat_mul8, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, off, BitVec.add_assoc,
    BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add, Nat.add_assoc]

/-! ## The loop of `mulAddRow` -/

/-- After `j` steps of `mulAddRow`'s loop from the state `s₀`. -/
structure RowInv (s₀ : State) (B : Addr) (Z eA eb : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : wv t.mem B eA j + 2 ^ (64 * j) * (t.gpr .rbp).toNat =
    wv s₀.mem B eA j + (s₀.gpr .rcx).toNat * wv s₀.mem B eb j

theorem rowStep_ok {s₀ : State} {B : Addr} {Z w eA eb : Nat}
    (h8 : s₀.gpr .r8 = off B eA) (h9 : s₀.gpr .r9 = off B eb) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * w ≤ eb ∨ eb + 8 * w ≤ eA) {j : Nat} (hj : j < w) {t : State}
    (hI : RowInv s₀ B Z eA eb j t) :
    WP isa (.block (mac .r9 0 ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ RowInv s₀ B Z eA eb (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t9 : t.gpr .r9 = off B eb := (hI.keep.gpr (by decide)).trans h9
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tcx : t.gpr .rcx = s₀.gpr .rcx := hI.keep.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (mac_ok t (src := .r9) (d := 0)
    (addr0 t9 hI.r14) (addr0 t8 hI.r14) (addr0 t8 hI.r14) (hI.scr.ld (by omega))
    (hI.scr.ld (by omega)) (hI.scr.st (by omega))) rfl) fun t₁ ⟨⟨lo, hm, hv⟩, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hk : Keep [.rax, .rdx, .rbp, .r14] s₀ t' :=
    ((hI.keep.trans k₁).trans k').mono (by decide)
  have hbp : t'.gpr .rbp = t₁.gpr .rbp := k'.gpr (by decide)
  have hmem : t'.mem = t.mem.writeW (off B (eA + 8 * j)) lo := hm'.trans hm
  -- The words read: `x` of the accumulator and `y` of `B`, both as on entry.
  have hx : t.mem.readW (off B (eA + 8 * j)) 64 = word s₀.mem B (eA + 8 * j) :=
    hI.out.word (Or.inr (Nat.le_refl _)) (by omega)
  have hy : t.mem.readW (off B (eb + 8 * j)) 64 = word s₀.mem B (eb + 8 * j) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), hk, h14, ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, wv_writeW_top _ _ _ _ _ (by omega), hbp]
    simp only [wv]
    rw [hx, hy, tcx] at hv
    have hval := hI.val
    rw [pow64_succ]
    zify at hv hval ⊢
    linear_combination (2 ^ (64 * j) : ℤ) * hv + hval

theorem rowTop_ok {t : State} {B : Addr} {Z w eA : Nat} (hs : Scr t B Z)
    (h8 : t.gpr .r8 = off B eA) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hA : eA + 8 * w + 16 ≤ Z) :
    WP isa (.block rowTop) t fun t' =>
      t'.mem = (t.mem.writeW (off B (eA + 8 * w)) (word t.mem B (eA + 8 * w) + t.gpr .rbp)).writeW
        (off B (eA + 8 * w + 8)) (word t.mem B (eA + 8 * w + 8) + 0 +
          (BitVec.ofBool (decide (2 ^ 64 ≤ (word t.mem B (eA + 8 * w)).toNat +
            (t.gpr .rbp).toNat))).setWidth 64) ∧ Keep [.rax] t t' := by
  have hn := hs.nowrap
  have hX : (t.mem.writeW (off B (eA + 8 * w)) (word t.mem B (eA + 8 * w) + t.gpr .rbp)).readW
      (off B (eA + 8 * w + 8)) 64 = word t.mem B (eA + 8 * w + 8) :=
    (writeW_outside t.mem B _ (by omega)).word (Or.inr (Nat.le_refl _)) (by omega)
  refine WP.keep [.rax] ?_ rfl
  unfold rowTop
  xrun [State.ea, ix, addr0 h8 h12, addr8 h8 h12, hs.ld (show eA + 8 * w + 8 ≤ Z by omega),
    hs.st (show eA + 8 * w + 8 ≤ Z by omega), hs.ld (show eA + 8 * w + 8 + 8 ≤ Z by omega),
    hs.st (show eA + 8 * w + 8 + 8 ≤ Z by omega), hX, sx0]

/-- The value after `rowTop`: `X + c` and `Y` plus its carry, if they fit. -/
theorem rowTop_val (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64)
    (hfit : (word m B (eA + 8 * w)).toNat + c.toNat + 2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat < 2 ^ 128) :
    wv ((m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)).writeW
        (off B (eA + 8 * w + 8)) (word m B (eA + 8 * w + 8) + 0 +
          (BitVec.ofBool (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat))).setWidth 64))
        B eA (w + 2) =
      wv m B eA w + 2 ^ (64 * w) * ((word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat) := by
  have o1 := writeW_outside m B (word m B (eA + 8 * w) + c) (d := eA + 8 * w) (by omega)
  have o2 := writeW_outside (m.writeW (off B (eA + 8 * w)) (word m B (eA + 8 * w) + c)) B
    (word m B (eA + 8 * w + 8) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat))).setWidth 64)
    (d := eA + 8 * w + 8) (by omega)
  have hc := addc_toNat (word m B (eA + 8 * w)) (word m B (eA + 8 * w + 8)) c (by omega)
  rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega,
    word_writeW_self, o2.word (Or.inl (Nat.le_refl _)) (by omega), word_writeW_self,
    o2.wv (Or.inl (by omega)) (by omega), o1.wv (Or.inl (Nat.le_refl _)) (by omega), pow64_succ, ← hc]
  ring

/-- `acc += rcx · B` (`mulAddRow`), if the sum fits in `w + 2` words. -/
theorem mulAddRow_ok {s : State} {B : Addr} {Z w eA eb : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h9 : s.gpr .r9 = off B eb) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hb : eb + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eb ∨ eb + 8 * w ≤ eA)
    (hbound : wv s.mem B eA (w + 2) + (s.gpr .rcx).toNat * wv s.mem B eb w < 2 ^ (64 * (w + 2))) :
    WP isa mulAddRow s fun t =>
      wv t.mem B eA (w + 2) = wv s.mem B eA (w + 2) + (s.gpr .rcx).toNat * wv s.mem B eb w ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ Keep [.rax, .rdx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  unfold mulAddRow
  -- `rbp := 0`.
  refine WP.seq (WP.mono (WP.keep [.rbp] (Q := fun t => t.gpr .rbp = 0 ∧ t.mem = s.mem)
    (by xrun) rfl) fun s₁ ⟨⟨hbp, hm₁⟩, k₁⟩ => ?_)
  have s₁8 : s₁.gpr .r8 = off B eA := (k₁.gpr (by decide)).trans h8
  have s₁9 : s₁.gpr .r9 = off B eb := (k₁.gpr (by decide)).trans h9
  have s₁12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have s₁cx : s₁.gpr .rcx = s.gpr .rcx := k₁.gpr (by decide)
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      RowInv s₁ B Z eA eb 0 t := by
    intro t h14 hm k _
    refine ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by simp), h14, by rw [hm]; exact Outside.refl _ _ _ _, ?_⟩
    rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp), hbp]
    rfl
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (RowInv s₁ B Z eA eb) h0
    (fun j _ hj t hI => rowStep_ok s₁8 s₁9 s₁12 (by omega) (by omega) hb (by omega) hj hI))
    fun t hI => ?_)
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans s₁8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans s₁12
  refine WP.mono (rowTop_ok hI.scr t8 t12 (by omega)) fun t' ⟨hm', k'⟩ => ?_
  -- The words above the loop's, as on entry.
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (Or.inr (Nat.le_refl _)) (by omega), hm₁]
  have hY : word t.mem B (eA + 8 * w + 8) = word s.mem B (eA + 8 * w + 8) := by
    rw [hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hval := hI.val
  rw [hm₁, s₁cx] at hval
  have e2 : wv s.mem B eA (w + 2) = wv s.mem B eA w + 2 ^ (64 * w) *
      ((word s.mem B (eA + 8 * w)).toNat + 2 ^ 64 * (word s.mem B (eA + 8 * w + 8)).toNat) := by
    rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, pow64_succ, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega]
    ring
  -- The sum fits: `X + c + 2⁶⁴ Y < 2¹²⁸`.
  have hfit : (word t.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
      2 ^ 64 * (word t.mem B (eA + 8 * w + 8)).toNat < 2 ^ 128 := by
    rw [hX, hY]
    have hlt : 2 ^ (64 * w) * ((word s.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
        2 ^ 64 * (word s.mem B (eA + 8 * w + 8)).toNat) < 2 ^ (64 * w) * 2 ^ 128 := by
      rw [← Nat.pow_add, show 64 * w + 128 = 64 * (w + 2) by omega]
      have := wv_lt t.mem B eA w
      zify at hval hbound e2 this ⊢
      linarith
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine ⟨?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', rowTop_val t.mem B hn (show eA + 8 * w + 16 ≤ Z by omega) _ hfit, hX, hY, e2]
    zify at hval ⊢
    linear_combination hval
  · rw [hm']
    intro x hx
    rw [writeW_outside _ B _ (by omega) x (by omega), writeW_outside _ B _ (by omega) x (by omega)]
    exact (hI.out x (by omega)).trans (by rw [hm₁])

end VG.Proof.Bignum.X86_64
