import VerifiedGarbage.Proof.Bignum.X86_64.Row

/-!
# Multiword arithmetic on x86-64: `acc := (acc + u m) / 2⁶⁴`

`reduceRow` adds `u m` to the accumulator `T` (`w + 2` words at `r8`),
`u = T₀ (-m⁻¹) mod 2⁶⁴` (`-m⁻¹` in `r15`, `m` the `w` words at `r10`), so
that the low word is zero, and stores the sum shifted down one word:
`2⁶⁴ T' = T + u m` (`reduceRow_ok`).

* `redHead` computes `u` into `rcx` and the carry of `T₀ + u m₀`.
* The loop, for `j = 1, …, w - 1`, is a multiply-accumulate step storing
  word `j - 1` (`RedInv`).
* `redTop` adds the carry into words `w` and `w + 1`, stored one down.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `t₀ + (t₀ m' mod 2⁶⁴) m ≡ 0 (mod 2⁶⁴)` when `m m' ≡ -1`. -/
theorem mont_low (t0 minv m : Nat) (h : (m * minv + 1) % 2 ^ 64 = 0) :
    (t0 * minv % 2 ^ 64 * m + t0) % 2 ^ 64 = 0 := by
  rw [Nat.add_mod, Nat.mul_mod (t0 * minv % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod,
    show t0 * minv * m + t0 = t0 * (m * minv + 1) by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc, Nat.mul_comm minv m],
    Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]

theorem redHead_ok {s : State} {B : Addr} {Z eA eN : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h10 : s.gpr .r10 = off B eN) (hA : eA + 8 ≤ Z) (hN : eN + 8 ≤ Z)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0) :
    WP isa (.block redHead) s fun t =>
      t.mem = s.mem ∧
      (t.gpr .rcx).toNat = (word s.mem B eA).toNat * (s.gpr .r15).toNat % 2 ^ 64 ∧
      2 ^ 64 * (t.gpr .rbp).toNat = (t.gpr .rcx).toNat * (word s.mem B eN).toNat + (word s.mem B eA).toNat ∧
      Keep [.rax, .rcx, .rdx, .rbp] s t := by
  refine WP.mono (WP.keep [.rax, .rcx, .rdx, .rbp] (c := .block redHead) (Q := fun t => t.mem = s.mem ∧
      (t.gpr .rcx).toNat = (word s.mem B eA).toNat * (s.gpr .r15).toNat % 2 ^ 64 ∧
      2 ^ 64 * (t.gpr .rbp).toNat = (t.gpr .rcx).toNat * (word s.mem B eN).toNat + (word s.mem B eA).toNat)
    ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2, k⟩
  unfold redHead
  xrun [State.ea, at0, h8, h10, off, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero,
    hs.ld hA, hs.ld hN, sx0]
  dsimp only [word, off] at hinv ⊢
  generalize s.mem.readW (B + BitVec.ofNat 64 eA) 64 = T0 at hinv ⊢
  generalize s.mem.readW (B + BitVec.ofNat 64 eN) 64 = N0 at hinv ⊢
  generalize s.gpr .r15 = mi at hinv ⊢
  refine ⟨BitVec.toNat_ofNat _ _, ?_⟩
  have hu : (BitVec.ofNat 64 (T0.toNat * mi.toNat)).toNat = T0.toNat * mi.toNat % 2 ^ 64 :=
    BitVec.toNat_ofNat _ _
  generalize hU : BitVec.ofNat 64 (T0.toNat * mi.toNat) = u at hu ⊢
  have hm := mul_toNat N0 u
  have hl := mul_le N0 u
  have hT := T0.isLt
  have hc := addc_toNat (BitVec.ofNat 64 (N0.toNat * u.toNat)) (BitVec.ofNat 64 (N0.toNat * u.toNat / 2 ^ 64))
    T0 (by omega)
  have hlow : (BitVec.ofNat 64 (N0.toNat * u.toNat) + T0).toNat = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_add_mod, hu, Nat.mul_comm N0.toNat]
    exact mont_low _ _ _ hinv
  rw [hlow] at hc
  rw [Nat.mul_comm u.toNat]
  omega

/-! ## The loop -/

/-- After the steps up to `j - 1` of `reduceRow`'s loop from the state `s₁`
(after `redHead`): words `0, …, j - 2` hold the low words of
`(T + u m) / 2⁶⁴` so far, and `rbp` the carry. -/
structure RedInv (s₁ : State) (B : Addr) (Z eA eN : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rbp, .r14] s₁ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eA (8 * (j - 1)) s₁.mem t.mem
  val : 2 ^ 64 * (wv t.mem B eA (j - 1) + 2 ^ (64 * (j - 1)) * (t.gpr .rbp).toNat) =
    wv s₁.mem B eA j + (s₁.gpr .rcx).toNat * wv s₁.mem B eN j

theorem redStep_ok {s₁ : State} {B : Addr} {Z w eA eN : Nat}
    (h8 : s₁.gpr .r8 = off B eA) (h10 : s₁.gpr .r10 = off B eN) (h12 : s₁.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eA + 8 * w ≤ eN ∨ eN + 8 * w ≤ eA) {j : Nat} (hj1 : 1 ≤ j) (hj : j < w) {t : State}
    (hI : RedInv s₁ B Z eA eN j t) :
    WP isa (.block (mac .r10 (-8) ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t fun t' =>
      t'.zf = some (decide (j + 1 = w)) ∧ RedInv s₁ B Z eA eN (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have t10 : t.gpr .r10 = off B eN := (hI.keep.gpr (by decide)).trans h10
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have tcx : t.gpr .rcx = s₁.gpr .rcx := hI.keep.gpr (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rdx, .rbp] (mac_ok t (src := .r10) (d := -8)
    (addr0 t10 hI.r14) (addr0 t8 hI.r14) (addrm8 t8 hI.r14 hj1) (hI.scr.ld (by omega))
    (hI.scr.ld (by omega)) (hI.scr.st (by omega))) rfl) fun t₁ ⟨⟨lo, hm, hv⟩, k₁⟩ => ?_
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hk : Keep [.rax, .rdx, .rbp, .r14] s₁ t' := ((hI.keep.trans k₁).trans k').mono (by decide)
  have hbp : t'.gpr .rbp = t₁.gpr .rbp := k'.gpr (by decide)
  have hmem : t'.mem = t.mem.writeW (off B (eA + 8 * (j - 1))) lo := hm'.trans hm
  have hx : t.mem.readW (off B (eA + 8 * j)) 64 = word s₁.mem B (eA + 8 * j) :=
    hI.out.word (Or.inr (by omega)) (by omega)
  have hy : t.mem.readW (off B (eN + 8 * j)) 64 = word s₁.mem B (eN + 8 * j) :=
    hI.out.word (by omega) (by omega)
  refine ⟨hI.scr.congr (k'.2.2.trans k₁.2.2), hk, h14, ?_, ?_⟩
  · rw [hmem]
    refine fun x hx' => ?_
    rw [writeW_outside t.mem B lo (by omega) x (by omega)]
    exact hI.out x (by omega)
  · rw [hmem, show j + 1 - 1 = j - 1 + 1 by omega, wv_writeW_top _ _ _ _ _ (by omega), hbp]
    simp only [wv]
    rw [hx, hy, tcx] at hv
    have hval := hI.val
    have hp : 2 ^ 64 * 2 ^ (64 * (j - 1)) = 2 ^ (64 * j) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [show 64 * (j - 1 + 1) = 64 * j by omega]
    zify at hv hval hp ⊢
    linear_combination hval + (2 ^ (64 * j) : ℤ) * hv + ((lo.toNat : ℤ) - (t.gpr .rbp).toNat) * hp

/-! ## The top words -/

/-- The memory `redTop` leaves: `X + c` at word `w - 1`, `Y` plus the carry
at word `w`, 0 at word `w + 1`, for the words `X`, `Y` at `w`, `w + 1`. -/
def redTopMem (m : Mem) (B : Addr) (eA w : Nat) (c : BitVec 64) : Mem :=
  ((m.writeW (off B (eA + 8 * (w - 1))) (word m B (eA + 8 * w) + c)).writeW (off B (eA + 8 * w))
    (word m B (eA + 8 * w + 8) + 0 +
      (BitVec.ofBool (decide (2 ^ 64 ≤ (word m B (eA + 8 * w)).toNat + c.toNat))).setWidth 64)).writeW
    (off B (eA + 8 * w + 8)) (0 : BitVec 64)

theorem redTop_ok {t : State} {B : Addr} {Z w eA : Nat} (hs : Scr t B Z) (hw : 1 ≤ w)
    (h8 : t.gpr .r8 = off B eA) (h12 : t.gpr .r12 = BitVec.ofNat 64 w) (hA : eA + 8 * w + 16 ≤ Z) :
    WP isa (.block redTop) t fun t' => t'.mem = redTopMem t.mem B eA w (t.gpr .rbp) ∧ Keep [.rax] t t' := by
  have hn := hs.nowrap
  have hY : (t.mem.writeW (off B (eA + 8 * (w - 1))) (word t.mem B (eA + 8 * w) + t.gpr .rbp)).readW
      (off B (eA + 8 * w + 8)) 64 = word t.mem B (eA + 8 * w + 8) :=
    (writeW_outside t.mem B _ (by omega)).word (Or.inr (by omega)) (by omega)
  refine WP.mono (WP.keep [.rax] (c := .block redTop) (Q := fun t' =>
    t'.mem = redTopMem t.mem B eA w (t.gpr .rbp)) ?_ rfl) fun t' ⟨h, k⟩ => ⟨h, k⟩
  unfold redTop redTopMem
  xrun [State.ea, ix, addr0 h8 h12, addr8 h8 h12, addrm8 h8 h12 hw,
    hs.ld (show eA + 8 * w + 8 ≤ Z by omega), hs.st (show eA + 8 * w + 8 ≤ Z by omega),
    hs.st (show eA + 8 * (w - 1) + 8 ≤ Z by omega),
    hs.ld (show eA + 8 * w + 8 + 8 ≤ Z by omega), hs.st (show eA + 8 * w + 8 + 8 ≤ Z by omega), hY, sx0]
  rfl

/-- The value after `redTop`, times `2⁶⁴`, if the top fits. -/
theorem redTop_val (m : Mem) (B : Addr) {Z eA w : Nat} (hn : B.toNat + Z ≤ 2 ^ 64) (hw : 1 ≤ w)
    (hA : eA + 8 * w + 16 ≤ Z) (c : BitVec 64)
    (hfit : (word m B (eA + 8 * w)).toNat + c.toNat + 2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat < 2 ^ 128) :
    2 ^ 64 * wv (redTopMem m B eA w c) B eA (w + 2) =
      2 ^ 64 * wv m B eA (w - 1) + 2 ^ (64 * w) * ((word m B (eA + 8 * w)).toNat + c.toNat +
        2 ^ 64 * (word m B (eA + 8 * w + 8)).toNat) := by
  unfold redTopMem
  generalize hX : word m B (eA + 8 * w) = X at hfit
  generalize hY : word m B (eA + 8 * w + 8) = Y at hfit
  have o1 := writeW_outside m B (X + c) (d := eA + 8 * (w - 1)) (by omega)
  have o2 := writeW_outside (m.writeW (off B (eA + 8 * (w - 1))) (X + c)) B
    (Y + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ X.toNat + c.toNat))).setWidth 64) (d := eA + 8 * w) (by omega)
  have o3 := writeW_outside ((m.writeW (off B (eA + 8 * (w - 1))) (X + c)).writeW (off B (eA + 8 * w))
    (Y + 0 + (BitVec.ofBool (decide (2 ^ 64 ≤ X.toNat + c.toNat))).setWidth 64)) B (0 : BitVec 64)
    (d := eA + 8 * w + 8) (by omega)
  have hc := addc_toNat X Y c (by omega)
  have hp : 2 ^ 64 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
  rw [show w + 2 = w - 1 + 1 + 1 + 1 by omega, wv, wv, wv, show eA + 8 * (w - 1 + 1 + 1) = eA + 8 * w + 8 by omega,
    show eA + 8 * (w - 1 + 1) = eA + 8 * w by omega, word_writeW_self,
    o3.word (Or.inl (Nat.le_refl _)) (by omega), word_writeW_self,
    o3.word (Or.inl (by omega)) (by omega), o2.word (Or.inl (by omega)) (by omega), word_writeW_self,
    o3.wv (Or.inl (by omega)) (by omega), o2.wv (Or.inl (by omega)) (by omega),
    o1.wv (Or.inl (Nat.le_refl _)) (by omega), show 64 * (w - 1 + 1 + 1) = 64 * w + 64 by omega,
    show 64 * (w - 1 + 1) = 64 * w by omega, Nat.pow_add]
  rw [show (0 : BitVec 64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, ← hc]
  zify at hp ⊢
  linear_combination ((X + c).toNat : ℤ) * hp

/-! ## The row -/

/-- `2⁶⁴ T' = T + u m` (`reduceRow`), for `u = T₀ (-m⁻¹) mod 2⁶⁴`, if `T + u m`
fits in `w + 2` words. -/
theorem reduceRow_ok {s : State} {B : Addr} {Z w eA eN : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B eA) (h10 : s.gpr .r10 = off B eN) (h12 : s.gpr .r12 = BitVec.ofNat 64 w)
    (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hA : eA + 8 * (w + 2) ≤ Z) (hN : eN + 8 * w ≤ Z)
    (hsep : eA + 8 * (w + 2) ≤ eN ∨ eN + 8 * w ≤ eA)
    (hinv : ((word s.mem B eN).toNat * (s.gpr .r15).toNat + 1) % 2 ^ 64 = 0)
    (hbound : ∀ u < 2 ^ 64, wv s.mem B eA (w + 2) + u * wv s.mem B eN w < 2 ^ (64 * (w + 2))) :
    WP isa reduceRow s fun t =>
      2 ^ 64 * wv t.mem B eA (w + 2) = wv s.mem B eA (w + 2) +
        (word s.mem B eA).toNat * (s.gpr .r15).toNat % 2 ^ 64 * wv s.mem B eN w ∧
      Outside B eA (8 * (w + 2)) s.mem t.mem ∧ Keep [.rax, .rcx, .rdx, .rbp, .r14] s t := by
  have hn := hs.nowrap
  unfold reduceRow
  refine WP.seq (WP.mono (redHead_ok hs h8 h10 (by omega) (by omega) hinv)
    fun s₁ ⟨hm₁, hu, hc₁, k₁⟩ => ?_)
  have s₁8 : s₁.gpr .r8 = off B eA := (k₁.gpr (by decide)).trans h8
  have s₁10 : s₁.gpr .r10 = off B eN := (k₁.gpr (by decide)).trans h10
  have s₁12 : s₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans h12
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 1 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      RedInv s₁ B Z eA eN 1 t := by
    intro t h14 hm k _
    refine ⟨hs.congr (k.2.2.trans k₁.2.2), k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _, ?_⟩
    rw [(k.gpr (by decide) : t.gpr .rbp = s₁.gpr .rbp)]
    simp only [wv, Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.add_zero]
    rw [hc₁, hm₁]
    omega
  refine WP.seq (WP.mono (wordLoop_ok (start := 1) (N := w) (by omega) hw'
    (RedInv s₁ B Z eA eN) h0
    (fun j hj1 hj t hI => redStep_ok s₁8 s₁10 s₁12 (by omega) (by omega) hN (by omega) hj1 hj hI))
    fun t hI => ?_)
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans s₁8
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans s₁12
  refine WP.mono (redTop_ok hI.scr (by omega) t8 t12 (by omega)) fun t' ⟨hm', k'⟩ => ?_
  have hX : word t.mem B (eA + 8 * w) = word s.mem B (eA + 8 * w) := by
    rw [hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hY : word t.mem B (eA + 8 * w + 8) = word s.mem B (eA + 8 * w + 8) := by
    rw [hI.out.word (Or.inr (by omega)) (by omega), hm₁]
  have hval := hI.val
  rw [hm₁] at hval
  have hb := hbound _ (s₁.gpr .rcx).isLt
  have e2 : wv s.mem B eA (w + 2) = wv s.mem B eA w + 2 ^ (64 * w) *
      ((word s.mem B (eA + 8 * w)).toNat + 2 ^ 64 * (word s.mem B (eA + 8 * w + 8)).toNat) := by
    rw [show w + 2 = w + 1 + 1 from rfl, wv, wv, pow64_succ, show eA + 8 * (w + 1) = eA + 8 * w + 8 by omega]
    ring
  have hp : 2 ^ 64 * 2 ^ (64 * (w - 1)) = 2 ^ (64 * w) := by rw [← Nat.pow_add]; congr 1; omega
  -- The top fits.
  have hfit : (word t.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
      2 ^ 64 * (word t.mem B (eA + 8 * w + 8)).toNat < 2 ^ 128 := by
    rw [hX, hY]
    have hlt : 2 ^ (64 * w) * ((word s.mem B (eA + 8 * w)).toNat + (t.gpr .rbp).toNat +
        2 ^ 64 * (word s.mem B (eA + 8 * w + 8)).toNat) < 2 ^ (64 * w) * 2 ^ 128 := by
      rw [← Nat.pow_add, show 64 * w + 128 = 64 * (w + 2) by omega]
      zify at hval hb e2 hp ⊢
      nlinarith [wv_lt t.mem B eA (w - 1)]
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine ⟨?_, ?_, ((k₁.trans hI.keep).trans k').mono (by decide)⟩
  · rw [hm', redTop_val t.mem B hn (by omega) (show eA + 8 * w + 16 ≤ Z by omega) _ hfit, hX, hY, e2, ← hu]
    zify at hval hp ⊢
    linear_combination hval - ((t.gpr .rbp).toNat : ℤ) * hp
  · rw [hm']
    intro x hx
    unfold redTopMem
    rw [writeW_outside _ B _ (by omega) x (by omega), writeW_outside _ B _ (by omega) x (by omega),
      writeW_outside _ B _ (by omega) x (by omega)]
    exact (hI.out x (by omega)).trans (by rw [hm₁])

end VG.Proof.Bignum.X86_64
