import VerifiedGarbage.Proof.Bignum.X86_64.MontMul

/-!
# Multiword arithmetic on x86-64: doubling modulo `m`

`double mo acc tmp o`: `[o] := 2 [o] mod m` for `[o] < m` (`double_ok`): the
double into the accumulator (`w + 1` words, the carry chain's carry kept in
`rbp` as in `subMod`), then `subMod` and `selectAcc`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

/-- `adc`, as numbers. -/
theorem adc_toNat (a b : BitVec 64) (c : Bool) :
    (a + b + (BitVec.ofBool c).setWidth 64).toNat + 2 ^ 64 *
      (decide (2 ^ 64 ≤ a.toNat + b.toNat + c.toNat)).toNat = a.toNat + b.toNat + c.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have hc : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by cases c <;> rfl
  have hc1 := Bool.toNat_le c
  rw [BitVec.toNat_add, BitVec.toNat_add, hc]
  by_cases h : 2 ^ 64 ≤ a.toNat + b.toNat + c.toNat <;> simp only [h, decide_true, decide_false,
    Bool.toNat_true, Bool.toNat_false] <;> omega

/-- After `j` words of `double`'s loop: `A_j + 2^(64 j) c = 2 O_j`. -/
structure DblInv (s₀ : State) (B : Addr) (Z eA eo : Nat) (j : Nat) (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rbp, .r14] s₀ t
  r14 : t.gpr .r14 = BitVec.ofNat 64 j
  out : Outside B eA (8 * j) s₀.mem t.mem
  val : ∃ c : Bool, t.gpr .rbp = mask c ∧
    wv t.mem B eA j + 2 ^ (64 * j) * c.toNat = 2 * wv s₀.mem B eo j

theorem dblStep_ok {s₀ : State} {B : Addr} {Z w eA eo : Nat}
    (h8 : s₀.gpr .r8 = off B eA) (hbx : s₀.gpr .rbx = off B eo) (h12 : s₀.gpr .r12 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 32) (hA : eA + 8 * w ≤ Z) (ho : eo + 8 * w ≤ Z)
    (sA : eo + 8 * w ≤ eA ∨ eA + 8 * w ≤ eo) {j : Nat} (hj : j < w) {t : State}
    (hI : DblInv s₀ B Z eA eo j t) :
    WP isa (.block ([cfFromRbp, .mov .rax (.mem (ix .rbx .r14)), .alu .adc .rax (.reg .rax),
        .store (ix .r8 .r14) .rax, cfToRbp] ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r12)] : List Instr))) t
      fun t' => t'.zf = some (decide (j + 1 = w)) ∧ DblInv s₀ B Z eA eo (j + 1) t' := by
  have hn := hI.scr.nowrap
  have t8 : t.gpr .r8 = off B eA := (hI.keep.gpr (by decide)).trans h8
  have tbx : t.gpr .rbx = off B eo := (hI.keep.gpr (by decide)).trans hbx
  have t12 : t.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  obtain ⟨c, hbp, hval⟩ := hI.val
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .rbp] (Q := fun t₁ =>
      ∃ c' : Bool, t₁.gpr .rbp = mask c' ∧ ∃ r : BitVec 64, t₁.mem = t.mem.writeW (off B (eA + 8 * j)) r ∧
        r.toNat + 2 ^ 64 * c'.toNat = 2 * (word t.mem B (eo + 8 * j)).toNat + c.toNat) ?_ rfl)
    fun t₁ ⟨⟨c', h₁, r, hm, hr⟩, k₁⟩ => ?_
  · unfold cfFromRbp cfToRbp
    xrun [State.ea, ix, addr0 t8 hI.r14, addr0 tbx hI.r14, hbp, cf_mask,
      hI.scr.ld (show eo + 8 * j + 8 ≤ Z by omega), hI.scr.st (show eA + 8 * j + 8 ≤ Z by omega)]
    refine ⟨_, rfl, _, rfl, ?_⟩
    rw [adc_toNat]
    show (word t.mem B (eo + 8 * j)).toNat + (word t.mem B (eo + 8 * j)).toNat + c.toNat = _
    omega
  have t₁14 : t₁.gpr .r14 = BitVec.ofNat 64 j := (k₁.gpr (by decide)).trans hI.r14
  have t₁12 : t₁.gpr .r12 = BitVec.ofNat 64 w := (k₁.gpr (by decide)).trans t12
  refine WP.mono (count_ok t₁ t₁14 t₁12 (by omega) (by omega)) fun t' ⟨hz, h14, hm', k'⟩ => ⟨hz, ?_⟩
  have hx : word t.mem B (eo + 8 * j) = word s₀.mem B (eo + 8 * j) := hI.out.word (by omega) (by omega)
  rw [hx] at hr
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

/-- `[o] := 2 [o] mod m`, for `[o] < m = [mo]`. -/
theorem double_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hs : Scr s B Z)
    (hdi : s.gpr .rdi = B) (hH : Hdr s.mem B w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    {mo acc tmp o : Nat} (hmo : mo < 8) (hacc : acc < 8) (htmp : tmp < 8) (ho : o < 8)
    (d1 : acc ≠ mo) (d2 : acc ≠ tmp) (d3 : acc ≠ o) (d6 : tmp ≠ mo) (d7 : tmp ≠ o)
    (hO : wv s.mem B (slot w o) w < wv s.mem B (slot w mo) w) :
    WP isa (double mo acc tmp o) s fun t =>
      wv t.mem B (slot w o) w = 2 * wv s.mem B (slot w o) w % wv s.mem B (slot w mo) w ∧
      Arrays B w [acc, tmp, o] s.mem t.mem ∧ Keep mmRegs s t := by
  have hn := hs.nowrap
  have sl : ∀ j < 8, slot w j + 8 * (w + 2) ≤ Z := fun j hj => (slot_le hj).trans hZ
  have sp : ∀ {j k}, j ≠ k → slot w j + 8 * (w + 2) ≤ slot w k ∨ slot w k + 8 * (w + 2) ≤ slot w j :=
    fun h => slot_sep h
  have hl : ∀ i < 32, InRegions (s.rd ++ s.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold double
  refine WP.seq (WP.mono (WP.keep [.rbx, .r10, .r8, .r12, .rsi, .rbp] (Q := fun t =>
      t.gpr .rbx = off B (slot w o) ∧ t.gpr .r10 = off B (slot w mo) ∧ t.gpr .r8 = off B (slot w acc) ∧
      t.gpr .r12 = BitVec.ofNat 64 w ∧ t.gpr .rsi = off B (slot w tmp) ∧ t.gpr .rbp = mask false ∧
      t.mem = s.mem)
    (by xrun [State.ea, hdr, hdi, hdrOff, hl (sArr o) (by unfold sArr; omega),
      hl (sArr mo) (by unfold sArr; omega), hl (sArr acc) (by unfold sArr; omega), hl sW (by decide),
      hl (sArr tmp) (by unfold sArr; omega), hH.harr o ho, hH.harr mo hmo, hH.harr acc hacc,
      hH.harr tmp htmp, hH.hw]) rfl)
    fun s₁ ⟨⟨hbx, h10, h8, h12, hsi₁, hbp, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  have h0 : ∀ t, t.gpr .r14 = BitVec.ofNat 64 0 → t.mem = s₁.mem → Keep [.r14] s₁ t → t.cf = s₁.cf →
      DblInv s₁ B Z (slot w acc) (slot w o) 0 t := fun t h14 hm k _ =>
    ⟨hs₁.congr k.2.2, k.mono (by decide), h14, by rw [hm]; exact Outside.refl _ _ _ _,
      ⟨false, (k.gpr (by decide)).trans hbp, by rw [hm]; rfl⟩⟩
  refine WP.seq (WP.mono (wordLoop_ok (start := 0) (N := w) (by omega) hw'
    (DblInv s₁ B Z (slot w acc) (slot w o)) h0
    (fun j _ hj t hI => dblStep_ok h8 hbx h12 (by omega) (by have := sl acc hacc; omega)
      (by have := sl o ho; omega) (by have := sp (Ne.symm d3); omega) hj hI)) fun s₂ hI => ?_)
  obtain ⟨c, hc, hval⟩ := hI.val
  have s₂8 : s₂.gpr .r8 = off B (slot w acc) := (hI.keep.gpr (by decide)).trans h8
  have s₂12 : s₂.gpr .r12 = BitVec.ofNat 64 w := (hI.keep.gpr (by decide)).trans h12
  have s₂di : s₂.gpr .rdi = B := ((k₁.trans hI.keep).gpr (by decide)).trans hdi
  have s₂si : s₂.gpr .rsi = off B (slot w tmp) := (hI.keep.gpr (by decide)).trans hsi₁
  refine WP.seq (WP.mono (WP.keep [.rax, .rbp] (Q := fun t => t.gpr .rsi = off B (slot w tmp) ∧
      ∃ v : BitVec 64, v.toNat = c.toNat ∧ t.mem = s₂.mem.writeW (off B (slot w acc + 8 * w)) v)
    (by
      unfold cfFromRbp
      xrun [State.ea, ix, s₂si, addr0 s₂8 s₂12, hc, cf_mask,
        hI.scr.st (show slot w acc + 8 * w + 8 ≤ Z by have := sl acc hacc; omega), sx0]
      refine ⟨_, ?_, rfl⟩
      cases c <;> rfl) rfl) fun s₃ ⟨⟨hsi, v, hv, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hI.scr.congr k₃.2.2
  have k13 := (hI.keep.trans k₃)
  have o3 : Outside B (slot w acc) (8 * (w + 1)) s₁.mem s₃.mem := by
    rw [hm₃]
    intro x hx
    rw [writeW_outside s₂.mem B v (by have := sl acc hacc; omega) x (by omega)]
    exact hI.out x (by omega)
  rw [hm₁] at o3
  have fN : wv s₃.mem B (slot w mo) w = wv s.mem B (slot w mo) w :=
    o3.wv (by have := sp (Ne.symm d1); omega) (by have := sl mo hmo; omega)
  have fO : wv s₁.mem B (slot w o) w = wv s.mem B (slot w o) w := by rw [hm₁]
  have hTl : wv s₃.mem B (slot w acc) w = wv s₂.mem B (slot w acc) w := by
    rw [hm₃]; exact (writeW_outside s₂.mem B v (by have := sl acc hacc; omega)).wv (Or.inl (by omega))
      (by have := sl acc hacc; omega)
  have hTw : (word s₃.mem B (slot w acc + 8 * w)).toNat = c.toNat := by
    rw [hm₃, word_writeW_self, hv]
  refine WP.seq (WP.mono (subMod_ok hs₃ ((k13.gpr (by decide)).trans h8) ((k13.gpr (by decide)).trans h10)
    hsi ((k13.gpr (by decide)).trans h12) (by omega) hw' (by have := sl acc hacc; omega)
    (by have := sl mo hmo; omega) (by have := sl tmp htmp; omega) (by have := sp d2; omega)
    (by have := sp d6; omega)) fun s₄ ⟨c', lt, hbp', hlt, hD, ho₄, k₄⟩ => ?_)
  have hs₄ := hs₃.congr k₄.2.2
  have k14 := k13.trans k₄
  refine WP.mono (selectAcc_ok hs₄ ((k14.gpr (by decide)).trans h8) ((k₄.gpr (by decide)).trans hsi)
    ((k14.gpr (by decide)).trans hbx) ((k14.gpr (by decide)).trans h12) hbp' (by omega) hw'
    (by have := sl acc hacc; omega) (by have := sl tmp htmp; omega) (by have := sl o ho; omega)
    (by have := sp (Ne.symm d3); omega) (by have := sp (Ne.symm d7); omega)) fun t ⟨hv', hot, k₅⟩ => ?_
  have hacc₄ : wv s₄.mem B (slot w acc) w = wv s₃.mem B (slot w acc) w :=
    ho₄.wv (by have := sp d2; omega) (by have := sl acc hacc; omega)
  rw [fN] at hD
  rw [fO] at hval
  have hN0 : 0 < wv s.mem B (slot w mo) w := by omega
  refine ⟨?_, ?_, ((k₁.trans k14).trans k₅).mono (by decide)⟩
  · rw [hv', hacc₄, hlt, hTw]
    have := VG.Proof.Bignum.csub_result (Tl := wv s₃.mem B (slot w acc) w) (Tw := c.toNat) (Tw1 := 0)
      (D := wv s₄.mem B (slot w tmp) w) (m := wv s.mem B (slot w mo) w) (R := 2 ^ (64 * w))
      (c := c'.toNat) (by have := wv_lt s.mem B (slot w mo) w; omega) (wv_lt _ _ _ _) (Bool.toNat_le c')
      (wv_lt _ _ _ _) (by rw [hTl, Nat.mul_zero, Nat.add_zero]; omega) hD
    rw [Nat.mul_zero, Nat.add_zero, hTl, hval] at this
    rw [← this]
    by_cases h : c.toNat < c'.toNat <;> simp [h, hTl]
  · have a3 : Arrays B w [acc, tmp, o] s.mem s₃.mem :=
      Arrays.of_outside (j := acc) (by simp) o3 (Nat.le_refl _) (by omega)
    have a4 : Arrays B w [acc, tmp, o] s₃.mem s₄.mem :=
      Arrays.of_outside (j := tmp) (by simp) ho₄ (Nat.le_refl _) (by omega)
    have a5 : Arrays B w [acc, tmp, o] s₄.mem t.mem :=
      Arrays.of_outside (j := o) (by simp) hot (Nat.le_refl _) (by omega)
    exact (a3.trans a4).trans a5

end VG.Proof.Bignum.X86_64
