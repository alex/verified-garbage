import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow

/-!
# Multiword arithmetic on x86-64: the BMI2/ADX Montgomery multiplication

`zeroWin` clears the `2 w + 2` words from the first window (`zeroWin_ok`);
the rows (`rows_ok`) keep the window `T < 2m` and
`2^(64 i) T ≡ (a mod 2^(64 i)) b (mod m)`, as the baseline's rounds do, the
window moving up a word a row; `montMulAdx_ok` is `montMul_ok` for it.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Bignum.X86_64.Adx
open VG.Proof.MlKem.X86_64 (Keep WP.keep)

/-! ## Clearing the windows -/

theorem wv_zero {m : Mem} {B : Addr} {d n : Nat} (h : ∀ k < n, word m B (d + 8 * k) = 0) : wv m B d n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wv, ih fun k hk => h k (by omega), h n (by omega)]; rfl

structure ZwInv (s₀ : State) (B : Addr) (Z A : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B A (8 * j) s₀.mem t.mem
  val : ∀ k < j, word t.mem B (A + 8 * k) = 0

/-- `zeroWin`: the `2 w + 2` words from `r8` cleared. -/
theorem zeroWin_ok {s : State} {B : Addr} {Z w A : Nat} (hs : Scr s B Z) (h8 : s.gpr .r8 = off B A)
    (hbx : s.gpr .rbx = BitVec.ofNat 64 w) (hw : w < 2 ^ 60) (hA : A + 8 * (2 * w + 2) ≤ Z) :
    WP isa zeroWin s fun t => (∀ k < 2 * w + 2, word t.mem B (A + 8 * k) = 0) ∧
      Outside B A (8 * (2 * w + 2)) s.mem t.mem ∧ Keep [.rax, .rcx, .r14] s t := by
  have hn := hs.nowrap
  unfold zeroWin
  refine WP.seq (WP.mono (WP.keep [.rax, .rcx, .r14] (Q := fun t => t.gpr .rax = 0 ∧
      t.gpr .rcx = BitVec.ofNat 64 (2 * w + 2) ∧ t.gpr .r14 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) ?_ rfl)
    fun s₁ ⟨⟨hax, hcx, h14, hm₁⟩, k₁⟩ => ?_)
  · have : BitVec.ofNat 64 w + BitVec.ofNat 64 w + 2 = BitVec.ofNat 64 (2 * w + 2) := by
      rw [← BitVec.ofNat_add, show (2 : BitVec 64) = BitVec.ofNat 64 2 from rfl, ← BitVec.ofNat_add]
      congr 1; omega
    xrun [hbx, this]
  have hs₁ := hs.congr k₁.2.2
  refine WP.mono (wp_upto (a := 0) (N := 2 * w + 2) (by omega) (ZwInv s₁ B Z A) ?_ (fun _ h => h)
    ⟨hs₁, Keep.refl _ _, h14, Outside.refl _ _ _ _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩)
    fun t hI => ⟨hI.val, hm₁ ▸ hI.out, (k₁.trans hI.keep).mono (by decide)⟩
  intro j _ hj t hI
  have t8 : t.gpr .r8 = off B A := (hI.keep.gpr (by decide)).trans ((k₁.gpr (by decide)).trans h8)
  have tax : t.gpr .rax = 0 := (hI.keep.gpr (by decide)).trans hax
  have tcx : t.gpr .rcx = BitVec.ofNat 64 (2 * w + 2) := (hI.keep.gpr (by decide)).trans hcx
  refine WP.mono (WP.keep [.r14] (Q := fun t' => t'.mem = t.mem.writeW (off B (A + 8 * j)) (0 : BitVec 64) ∧
      t'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧ t'.zf = some (decide (j + 1 = 2 * w + 2)))
    (by xrun [State.ea, ix, addr0 t8 hI.r14, hI.scr.st (show A + 8 * j + 8 ≤ Z by omega), tax, tcx,
      show t.gpr .r14 + 1 = BitVec.ofNat 64 (j + 1) by rw [hI.r14, ofNat_add_one],
      ofNat_sub_beq (show j + 1 < 2 ^ 64 by omega) (show 2 * w + 2 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm, h14', hz⟩, k'⟩ => ⟨hz, ?_⟩
  have o' := writeW_outside t.mem B (0 : BitVec 64) (d := A + 8 * j) (by omega)
  refine ⟨hI.scr.congr k'.2.2, (hI.keep.trans k').mono (by decide), h14', ?_, fun k hk => ?_⟩
  · rw [hm]
    exact (hI.out.mono (o' := A) (n' := 8 * (j + 1)) (Nat.le_refl _) (by omega)).trans
      (o'.mono (o' := A) (n' := 8 * (j + 1)) (by omega) (by omega))
  · rw [hm]
    by_cases hkj : k = j
    · subst hkj; exact word_writeW_self _ _ _ _
    · rw [o'.word (by omega) (by omega)]; exact hI.val k (by omega)

/-! ## The rows -/

/-- After rows `0, …, i - 1` from `s₀`: the window `T < 2m` at `A + 8 i`
(`A` the first), `2^(64 i) T ≡ (a mod 2^(64 i)) b (mod m)`, and the words
above the window zero. -/
structure RowsInv (s₀ : State) (B : Addr) (Z w a b : Nat) (i : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rsi, .rcx, .rbp, .r14, .r11, .r12, .r13, .r15, .r8] s₀ t
  r8 : t.gpr .r8 = off B (slot w aAcc + 16 + 8 * i)
  out : Outside B (slot w aAcc) (16 * (w + 2)) s₀.mem t.mem
  zero : ∀ j, i + w + 2 ≤ j → j < 2 * w + 2 → word t.mem B (slot w aAcc + 16 + 8 * j) = 0
  lt : wv t.mem B (slot w aAcc + 16 + 8 * i) (w + 2) < 2 * wv s₀.mem B (slot w aN) w
  cong : 2 ^ (64 * i) * wv t.mem B (slot w aAcc + 16 + 8 * i) (w + 2) % wv s₀.mem B (slot w aN) w =
    wv s₀.mem B (slot w a) i * wv s₀.mem B (slot w b) w % wv s₀.mem B (slot w aN) w

theorem rows_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {a b : Nat} (ha : a < 8) (hb : b < 8)
    (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hw4 : w % 4 = 0) (hw1 : 4 ≤ w) (hw : w < 2 ^ 60)
    (h8 : s.gpr .r8 = off B (slot w aAcc + 16)) (h9 : s.gpr .r9 = off B (slot w b))
    (h10 : s.gpr .r10 = off B (slot w aN)) (hbx : s.gpr .rbx = BitVec.ofNat 64 w)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (h0 : ∀ k < 2 * w + 2, word s.mem B (slot w aAcc + 16 + 8 * k) = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (.loop (row a) .ne) s (RowsInv s B Z w a b w) := by
  have hn := hs.nowrap
  have hA := slot_le (w := w) ha
  have hBs := slot_le (w := w) hb
  have hNs := slot_le (w := w) (show aN < 8 by decide)
  have hTs := slot_le (w := w) (show aTmp < 8 by decide)
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hg0 : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  have sbX : slot w b + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w b := by
    have := slot_sep (w := w) hb1; have := slot_sep (w := w) hb2; unfold slot aAcc aTmp at *; omega
  have saX : slot w a + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w a := by
    have := slot_sep (w := w) ha1; have := slot_sep (w := w) ha2; unfold slot aAcc aTmp at *; omega
  have sNX : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have hN0 : 0 < wv s.mem B (slot w aN) w := by omega
  refine wp_upto (a := 0) (N := w) (by omega) (RowsInv s B Z w a b) ?_ (fun _ h => h)
    ⟨hs, Keep.refl _ _, by rw [h8], Outside.refl _ _ _ _, fun j _ hj => h0 j hj,
      by rw [Nat.mul_zero, Nat.add_zero, wv_zero fun k hk => h0 k (by omega)]; omega,
      by rw [Nat.mul_zero, Nat.add_zero, wv_zero fun k hk => h0 k (by omega)]; simp [wv]⟩
  intro i _ hi t hI
  have hk := hI.keep
  have fw : ∀ {d}, d + 8 ≤ slot w aAcc ∨ slot w aAcc + 16 * (w + 2) ≤ d → d + 8 ≤ Z →
      word t.mem B d = word s.mem B d := fun h1 h2 => hI.out.word h1 (by omega)
  have fv : ∀ {d k}, d + 8 * k ≤ slot w aAcc ∨ slot w aAcc + 16 * (w + 2) ≤ d → d + 8 * k ≤ Z →
      wv t.mem B d k = wv s.mem B d k := fun h1 h2 => hI.out.wv h1 (by omega)
  have vN := fv (d := slot w aN) (k := w) (by omega) (by omega)
  have vB := fv (d := slot w b) (k := w) (by omega) (by omega)
  refine WP.mono (row_ok hI.scr ((hk.gpr (by decide)).trans hdi) (hH.of_outside hI.out hg0) hZ ha hb ha1 ha2 hb1
    hb2 rfl hi hw4 hw1 hw hI.r8 ((hk.gpr (by decide)).trans h9) ((hk.gpr (by decide)).trans h10)
    ((hk.gpr (by decide)).trans hbx)) fun t' ⟨hval, ho, h8', hz, k'⟩ => ⟨hz, ?_⟩
  obtain ⟨u, hu, hv⟩ := hval (by rw [fw (by omega) (by omega)]; exact hinv)
    (by rw [show slot w aAcc + 16 + 8 * i + 8 * (w + 2) = slot w aAcc + 16 + 8 * (i + w + 2) by omega];
        exact hI.zero _ (Nat.le_refl _) (by omega))
    (by rw [vN]; exact hI.lt) (by rw [vB, vN]; exact hB)
  rw [vN, vB, fw (by omega) (by omega)] at hv
  have e8 : slot w aAcc + 16 + 8 * i + 8 = slot w aAcc + 16 + 8 * (i + 1) := by omega
  rw [e8] at hv h8'
  refine ⟨hI.scr.congr k'.2.2, (hk.trans k').mono (by simp), h8',
    hI.out.trans (ho.mono (o' := slot w aAcc) (n' := 16 * (w + 2)) (by omega) (by omega)), fun j hj hj' => ?_,
    VG.Proof.Bignum.round_lt hv hI.lt (word s.mem B (slot w a + 8 * i)).isLt hB hu, ?_⟩
  · rw [ho.word (by omega) (by omega)]; exact hI.zero j (by omega) hj'
  · rw [show 64 * (i + 1) = 64 * i + 64 by omega, Nat.pow_add, VG.Proof.Bignum.round_step hv hI.cong]
    congr 1

/-! ## The multiplication -/

/-- `setup b`: `b`, `m`, the first window and `w` from the header. -/
theorem adxSetup_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {b : Nat} (hb : b < 8) :
    WP isa (.block (setup b)) s fun t => t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc + 16) ∧ t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.mem = s.mem ∧ Keep [.r9, .r10, .r8, .rbx] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.r9, .r10, .r8, .rbx] (Q := fun t => t.gpr .r9 = off B (slot w b) ∧
      t.gpr .r10 = off B (slot w aN) ∧ t.gpr .r8 = off B (slot w aAcc + 16) ∧ t.gpr .rbx = BitVec.ofNat 64 w ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold setup
  xrun [State.ea, hdr, hdi, hdrOff, hl (sArr b) (by unfold sArr; omega), hl (sArr aN) (by decide),
    hl (sArr aAcc) (by decide), hl sW (by decide), hH.harr b hb, hH.harr aN (by decide), hH.harr aAcc (by decide),
    hH.hw, off_add16]

/-- `finishBases o`: `w`, the result `aTmp`, `aAcc` and `o` from the header. -/
theorem finishBases_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) {o : Nat} (ho : o < 8) :
    WP isa (.block (finishBases o)) s fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rsi = off B (slot w aAcc) ∧ t.gpr .rbx = off B (slot w o) ∧
      t.mem = s.mem ∧ Keep [.r12, .r8, .rsi, .rbx] s t := by
  have hn := hs.nowrap
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.r12, .r8, .rsi, .rbx] (Q := fun t => t.gpr .r12 = BitVec.ofNat 64 w ∧
      t.gpr .r8 = off B (slot w aTmp) ∧ t.gpr .rsi = off B (slot w aAcc) ∧ t.gpr .rbx = off B (slot w o) ∧
      t.mem = s.mem) ?_ rfl) fun t ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold finishBases
  xrun [State.ea, hdr, hdi, hdrOff, hl sW (by decide), hl (sArr aTmp) (by decide), hl (sArr aAcc) (by decide),
    hl (sArr o) (by unfold sArr; omega), hH.hw, hH.harr aTmp (by decide), hH.harr aAcc (by decide), hH.harr o ho]

/-- `fused o a b`, for `w` a multiple of 4: what `montMul_ok` says of `montMul`. -/
theorem fused_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw4 : w % 4 = 0) (hw1 : 4 ≤ w)
    (hw : w < 2 ^ 31) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (fused o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => (slot_le hj).trans hZ
  have hAT : slot w aAcc + 8 * (w + 2) = slot w aTmp := by unfold slot aAcc aTmp; omega
  have hg0 : hdrBytes ≤ slot w aAcc := by unfold slot; omega
  have hTs := sl aTmp (by decide)
  have sNX : slot w aN + 8 * (w + 2) ≤ slot w aAcc := by unfold slot aN aAcc; omega
  have soX : slot w o + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w o := by
    have := slot_sep (w := w) ho1; have := slot_sep (w := w) ho2; unfold slot aAcc aTmp at *; omega
  have sbX : slot w b + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w b := by
    have := slot_sep (w := w) hb1; have := slot_sep (w := w) hb2; unfold slot aAcc aTmp at *; omega
  have saX : slot w a + 8 * (w + 2) ≤ slot w aAcc ∨ slot w aTmp + 8 * (w + 2) ≤ slot w a := by
    have := slot_sep (w := w) ha1; have := slot_sep (w := w) ha2; unfold slot aAcc aTmp at *; omega
  have hN0 : 0 < wv s.mem B (slot w aN) w := by omega
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold fused
  -- The bases.
  refine WP.seq (WP.mono (adxSetup_ok hs hdi hH hZ hb) fun s₁ ⟨h9, h10, h8, hbx, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  -- The windows := 0.
  refine WP.seq (WP.mono (zeroWin_ok hs₁ h8 hbx (by omega) (by omega)) fun s₂ ⟨hz₂, ho₂, k₂⟩ => ?_)
  rw [hm₁] at ho₂
  have hs₂ := hs₁.congr k₂.2.2
  have k12 := k₁.trans k₂
  have fw₂ : ∀ {d}, d + 8 ≤ slot w aAcc + 16 ∨ slot w aAcc + 16 + 8 * (2 * w + 2) ≤ d → d + 8 ≤ Z →
      word s₂.mem B d = word s.mem B d := fun h1 h2 => ho₂.word h1 (by omega)
  have fv₂ : ∀ {d k}, d + 8 * k ≤ slot w aAcc + 16 ∨ slot w aAcc + 16 + 8 * (2 * w + 2) ≤ d → d + 8 * k ≤ Z →
      wv s₂.mem B d k = wv s.mem B d k := fun h1 h2 => ho₂.wv h1 (by omega)
  have hH₂ : Hdr s₂.mem B w minv := hH.of_outside ho₂ (by omega)
  have vN := fv₂ (d := slot w aN) (k := w) (by omega) (by omega)
  have vA := fv₂ (d := slot w a) (k := w) (by omega) (by have := sl a ha; omega)
  have vB := fv₂ (d := slot w b) (k := w) (by omega) (by have := sl b hb; omega)
  -- The rows.
  refine WP.seq (WP.mono (rows_ok hs₂ ((k12.gpr (by decide)).trans hdi) hH₂ hZ ha hb ha1 ha2 hb1 hb2 hw4 hw1 (by omega)
    ((k₂.gpr (by decide)).trans h8) ((k₂.gpr (by decide)).trans h9) ((k₂.gpr (by decide)).trans h10)
    ((k₂.gpr (by decide)).trans hbx) (by rw [fw₂ (by omega) (by omega)]; exact hinv) hz₂
    (by rw [vB, vN]; exact hB)) fun s₃ hR => ?_)
  have hTlt := hR.lt
  have hTc := hR.cong
  rw [show slot w aAcc + 16 + 8 * w = slot w aTmp by omega, vN] at hTlt hTc
  rw [vA, vB] at hTc
  have k123 := k12.trans hR.keep
  have hs₃ := hR.scr
  have fr₃ : ∀ {d k}, d + 8 * k ≤ slot w aAcc ∨ slot w aAcc + 16 * (w + 2) ≤ d → d + 8 * k ≤ Z →
      wv s₃.mem B d k = wv s.mem B d k := fun h1 h2 =>
    (hR.out.wv h1 (by omega)).trans (fv₂ (by omega) (by omega))
  have hH₃ : Hdr s₃.mem B w minv := hH₂.of_outside hR.out hg0
  -- `T - m` into `aAcc`, and the one below `m` into `o`.
  unfold finish
  refine WP.seq (WP.mono (finishBases_ok hs₃ ((k123.gpr (by decide)).trans hdi) hH₃ hZ ho)
    fun s₄ ⟨h12₄, h8₄, hsi₄, hbx₄, hm₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have k14 := k123.trans k₄
  refine WP.seq (WP.mono (subMod_ok hs₄ h8₄ ((((k₂.trans hR.keep).trans k₄).gpr (by decide)).trans h10) hsi₄ h12₄ (by omega) hw
    (by omega) (by have := sl aN (by decide); omega) (by omega) (by omega) (by omega))
    fun s₅ ⟨c, lt, hbp, hlt, hD, ho₅, k₅⟩ => ?_)
  rw [hm₄] at hlt hD ho₅
  have hs₅ := hs₄.congr k₅.2.2
  refine WP.mono (selectAcc_ok hs₅ ((k₅.gpr (by decide)).trans h8₄) ((k₅.gpr (by decide)).trans hsi₄)
    ((k₅.gpr (by decide)).trans hbx₄) ((k₅.gpr (by decide)).trans h12₄) hbp (by omega) hw (by omega) (by omega)
    (by have := sl o ho; omega) (by omega) (by omega)) fun t ⟨hv, hot, k₆⟩ => ?_
  have hT₅ : wv s₅.mem B (slot w aTmp) w = wv s₃.mem B (slot w aTmp) w := ho₅.wv (by omega) (by omega)
  have hN₃ : wv s₃.mem B (slot w aN) w = wv s.mem B (slot w aN) w := fr₃ (by omega) (by omega)
  have hD' : wv s₅.mem B (slot w aAcc) w + wv s.mem B (slot w aN) w = wv s₃.mem B (slot w aTmp) w +
      2 ^ (64 * w) * c.toNat := by rw [← hN₃]; exact hD
  have hres : wv t.mem B (slot w o) w = wv s₃.mem B (slot w aTmp) (w + 2) % wv s.mem B (slot w aN) w := by
    rw [hv, hT₅, hlt, wv_top2]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w aTmp) w)
      (Tw := (word s₃.mem B (slot w aTmp + 8 * w)).toNat)
      (Tw1 := (word s₃.mem B (slot w aTmp + 8 * w + 8)).toNat) (D := wv s₅.mem B (slot w aAcc) w)
      (m := wv s.mem B (slot w aN) w) (R := 2 ^ (64 * w)) (c := c.toNat)
      (by have := wv_lt s.mem B (slot w aN) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c) (wv_lt _ _ _ _)
      (by rw [← wv_top2]; exact hTlt) hD'
    rw [← this]
    by_cases h : (word s₃.mem B (slot w aTmp + 8 * w)).toNat < c.toNat <;> simp [h]
  refine ⟨?_, ?_, ?_, ((k14.trans k₅).trans k₆).mono (by decide)⟩
  · rw [hres]; exact Nat.mod_lt _ hN0
  · rw [hres, Nat.mod_mul_mod, Nat.mul_comm, hTc]
  · have o₃ : Outside B (slot w aAcc) (16 * (w + 2)) s.mem s₃.mem := fun x hx =>
      (hR.out x hx).trans (ho₂ x (by omega))
    have o₅ : Outside B (slot w aAcc) (16 * (w + 2)) s.mem s₅.mem := fun x hx =>
      (ho₅ x (by omega)).trans (o₃ x hx)
    intro x hx
    have h1 := hx aAcc (by simp)
    have h2 := hx aTmp (by simp)
    have h3 := hx o (by simp)
    exact (hot x (by omega)).trans (o₅ x (by omega))

theorem rotr2_toNat (x : BitVec 64) : (x.rotateRight 2).toNat = x.toNat / 4 + x.toNat % 4 * 2 ^ 62 := by
  rw [BitVec.toNat_rotateRight]
  simp only [Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reduceSub]
  have hx := x.isLt
  rw [Nat.shiftLeft_eq, show x.toNat * 2 ^ 62 % 2 ^ 64 = (x.toNat % 4) <<< 62 by rw [Nat.shiftLeft_eq]; omega,
    Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  omega

/-- What `sizeTest` tests. -/
def SizeOk (w : Nat) : Prop := w % 4 = 0 ∧ 4 ≤ w ∧ w < 2 ^ 30 + 4

instance (w : Nat) : Decidable (SizeOk w) := inferInstanceAs (Decidable (_ ∧ _))

theorem sizeTest_beq (w : Nat) (hw : w < 2 ^ 64) :
    ((BitVec.ofNat 64 w - 4).rotateRight 2 >>> 28 == 0) = decide (SizeOk w) := by
  have h : ((BitVec.ofNat 64 w - 4).rotateRight 2 >>> 28).toNat =
      ((2 ^ 64 - 4 + w) % 2 ^ 64 / 4 + (2 ^ 64 - 4 + w) % 2 ^ 64 % 4 * 2 ^ 62) / 2 ^ 28 := by
    rw [BitVec.toNat_ushiftRight, rotr2_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub,
      show (4 : BitVec 64).toNat = 4 from rfl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  generalize hv : (2 ^ 64 - 4 + w) % 2 ^ 64 = v at h
  have h1 : v % 4 = w % 4 := by omega
  have h3 : 4 ≤ w → v = w - 4 := by omega
  have h4 : w < 4 → v = 2 ^ 64 - 4 + w := by omega
  unfold SizeOk
  by_cases h0 : w % 4 = 0 ∧ 4 ≤ w ∧ w < 2 ^ 30 + 4
  · simp only [h0, and_self, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, show (0 : BitVec 64).toNat = 0 from rfl]; omega
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; have := congrArg BitVec.toNat he; rw [h, show (0 : BitVec 64).toNat = 0 from rfl] at this
    omega

/-- `sizeTest`: ZF set when `fused` applies. -/
theorem sizeTest_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z) (hdi : s.gpr .rdi = B)
    (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) :
    WP isa (.block sizeTest) s fun t => t.zf = some (decide (SizeOk w)) ∧ t.mem = s.mem ∧ Keep [.rax] s t := by
  have hn := hs.nowrap
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.zf = some (decide (SizeOk w)) ∧ t.mem = s.mem) ?_ rfl)
    fun t ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold sizeTest
  xrun [State.ea, hdr, hdi, hdrOff, hs.ld (show 8 * sW + 8 ≤ Z by have := hdr_lt_slot w 8 (show sW < 32 by decide); omega),
    hH.hw, sizeTest_beq w (by unfold slot hdrBytes at hZ; omega)]

/-- `montMulAdx o a b`: what `montMul_ok` says of `montMul aN aAcc aTmp o a b`, if
neither `a` nor `b` is `aTmp` either. -/
theorem montMulAdx_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (ho1 : o ≠ aAcc) (ho2 : o ≠ aTmp) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp) (hb1 : b ≠ aAcc) (hb2 : b ≠ aTmp)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv s.mem B (slot w b) w < wv s.mem B (slot w aN) w) :
    WP isa (montMulAdx o a b) s fun t =>
      wv t.mem B (slot w o) w < wv s.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s.mem B (slot w aN) w =
        wv s.mem B (slot w a) w * wv s.mem B (slot w b) w % wv s.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  unfold montMulAdx
  refine WP.seq (WP.mono (sizeTest_ok hs hdi hH hZ) fun s₁ ⟨hz, hm₁, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have hdi₁ : s₁.gpr .rdi = B := (k₁.gpr (by decide)).trans hdi
  rw [← hm₁] at hinv hB hH ⊢
  have post : ∀ t, (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s₁ t) →
      (wv t.mem B (slot w o) w < wv s₁.mem B (slot w aN) w ∧
      wv t.mem B (slot w o) w * 2 ^ (64 * w) % wv s₁.mem B (slot w aN) w =
        wv s₁.mem B (slot w a) w * wv s₁.mem B (slot w b) w % wv s₁.mem B (slot w aN) w ∧
      Arrays B w [aAcc, aTmp, o] s₁.mem t.mem ∧ Keep mmRegs s t) :=
    fun t ⟨h1, h2, h3, k⟩ => ⟨h1, h2, h3, (k₁.trans k).mono (by decide)⟩
  by_cases h4 : SizeOk w
  · refine WP.ite true (by simp [eval, hz, h4]) (fun _ => WP.mono (fused_ok hs₁ hdi₁ hH hZ h4.1 h4.2.1 hw' ho ha hb
      ho1 ho2 ha1 ha2 hb1 hb2 hinv hB) post) (by simp)
  · refine WP.ite false (by simp [eval, hz, h4]) (by simp) (fun _ => WP.mono (montMul_ok hs₁ hdi₁ hH hZ hw hw'
      (by decide) (by decide) (by decide) ho ha hb (by decide) (by decide) (Ne.symm ho1) (Ne.symm ha1) (Ne.symm hb1)
      (by decide) (Ne.symm ho2) hinv hB) post)

end VG.Proof.Bignum.X86_64
