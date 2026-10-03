import VerifiedGarbage.Proof.Bignum.X86_64.PubR2

/-!
# `vg_rsa_public` on x86-64: the exponentiation

`Y := R mod m` and `X := x R mod m` from `R² mod m`, the exponentiation
(`Y ≡ x^e R`), and `Y R⁻¹ = x^e mod m` (`expPhase_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- The steps of the exponentiation. -/
def expSteps : List (Prog isa) := [mm aY aR2 aOne, mm aXm aX aR2, expLoop, mm aY aY aOne]

/-- What the exponentiation changes. -/
def expPhaseRanges (w : Nat) : List (Nat × Nat) := (slot w aXm, 8 * (w + 2)) :: expRanges w

theorem expPhaseRanges_arr (w : Nat) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ aXm) : ∀ r ∈ expPhaseRanges w, slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  have := hdr_lt_slot w j (show 31 < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  have s4 := slot_sep (w := w) h4
  have := hj
  simp only [expPhaseRanges, expRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sI, sV, sBit, sFn] at * <;> omega

theorem expPhaseRanges_le (w : Nat) : ∀ r ∈ expPhaseRanges w, r.1 + r.2 ≤ slot w 8 := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact slot_le (by decide)
  · exact expRanges_le w r hr

/-- A Montgomery multiplication `[o] := [a] [b] R⁻¹` that keeps the modulus. -/
theorem mmN_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) {o a b : Nat} (ho : o < 8) (ha : a < 8) (hb : b < 8)
    (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc) (d5 : o ≠ aN)
    (hn : wv t.mem B (slot w aN) w = N) (hinv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv t.mem B (slot w b) w < N) :
    WP isa (mm o a b) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (slot w aN) w = N ∧
      ((word t'.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem B (slot w o) w < N ∧
      wv t'.mem B (slot w o) w * 2 ^ (64 * w) % N = wv t.mem B (slot w a) w * wv t.mem B (slot w b) w % N ∧
      Arrays B w [aAcc, aTmp, o] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  have hnm : aN ∉ [aAcc, aTmp, o] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨by decide, by decide, Ne.symm d5⟩
  refine WP.mono (mm_ok hg hZ hw hw' ho ha hb d1 d2 d3 d4 hinv (by rw [hn]; exact hB))
    fun t' ⟨hg', hlt', hm, hA, k⟩ => ?_
  rw [hn] at hlt' hm
  exact ⟨hg', by rw [hA.wv_of_not_mem (by decide) hnm hn']; exact hn,
    by rw [hA.word0_of_not_mem (by decide) hnm hn' (by omega)]; exact hinv, hlt', hm, hA, k⟩

theorem Frm.ep_wv {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (expPhaseRanges w) m m')
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aY)
    (h4 : j ≠ aXm) : wv m' B (slot w j) w = wv m B (slot w j) w :=
  h.wv_eq (fun r hr => by have := expPhaseRanges_arr w hj h1 h2 h3 h4 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem Frm.ep_hdr {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (expPhaseRanges w) m m') {i : Nat}
    (hi : i < 32) (h0 : i ≠ sI) (h1 : i ≠ sV) (h2 : i ≠ sBit) : word m' B (8 * i) = word m B (8 * i) :=
  h.word_eq (fun r hr => by
    rcases List.mem_cons.mp hr with rfl | hr
    · have := hdr_lt_slot w aXm hi; omega
    · exact expRanges_hdr w hi h0 h1 h2 r hr) (by omega)

theorem Frm.ep_of_arrays {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ j ∈ js, j = aAcc ∨ j = aTmp ∨ j = aY ∨ j = aXm) : Frm B (expPhaseRanges w) m m' :=
  Frm.of_arrays h fun j hj => by
    rcases hjs j hj with rfl | rfl | rfl | rfl <;> simp [expPhaseRanges, expRanges, bitRanges]

/-- The exponentiation: `x^e mod m` into `[aY]`, for `[aR2] ≡ R²`. -/
theorem expPhase_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat} {ep : Addr} {L : Nat}
    {eb : List Byte} (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hodd : N % 2 = 1) (hN1 : 1 < N) (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hX : wv s.mem B (slot w aX) w = X) (hone : wv s.mem B (slot w aOne) w = 1)
    (hlt2 : wv s.mem B (slot w aR2) w < N)
    (hr2 : wv s.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N)
    (he : word s.mem B (8 * sE) = ep) (hlen : word s.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2 ^ 31) (heb : Src s B Z ep eb) :
    WP isa (seqs expSteps) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aY) w = X ^ Spec.Rsa.os2ip eb % N ∧
      Frm B (expPhaseRanges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  unfold expSteps
  -- `Y := R`.
  refine WP.seq (WP.mono (mmN_ok (o := aY) (a := aR2) (b := aOne) hg hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn hinv (by rw [hone]; exact hN1))
    fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  have f₁ := Frm.ep_of_arrays ha₁ (by simp)
  have hY₁ : wv t₁.mem B (slot w aY) w % N = 2 ^ (64 * w) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₁, hone, Nat.mul_one, hr2]
  -- `X := x R`.
  refine WP.seq (WP.mono (mmN_ok (o := aXm) (a := aX) (b := aR2) hg₁ hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn₁ hinv₁
    (by rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlt2))
    fun t₂ ⟨hg₂, hn₂, hinv₂, hlt₂, hm₂, ha₂, k₂⟩ => ?_)
  have f₂ := Frm.ep_of_arrays ha₂ (by simp)
  rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide),
    f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide), hX] at hm₂
  have hX₂ : wv t₂.mem B (slot w aXm) w % N = X * 2 ^ (64 * w) % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₂, Nat.mul_mod, hr2, ← Nat.mul_mod, Nat.mul_assoc]
  have hY₂ : wv t₂.mem B (slot w aY) w = wv t₁.mem B (slot w aY) w :=
    ha₂.wv_of_not_mem (by decide) (by decide) hn'
  -- The exponentiation.
  have f₁₂ := f₁.trans f₂
  have hs₂ : ∀ i < 32, i ≠ sI → i ≠ sV → i ≠ sBit → word t₂.mem B (8 * i) = word s.mem B (8 * i) :=
    fun i hi h0 h1 h2 => f₁₂.ep_hdr hi h0 h1 h2
  have hin₂ : InScr B Z s.mem t₂.mem :=
    InScr.of_frm f₁₂ fun r hr => (expPhaseRanges_le w r hr).trans hZ
  have heb₂ := heb.congrK hin₂ (k₁.trans k₂)
  refine WP.seq (WP.mono (expLoop_ok (x := X) (Y := wv t₂.mem B (slot w aY) w) ⟨hg₂, hn₂, hinv₂, rfl⟩ hZ hw hw' hR
    hlt₂ hX₂ rfl (by rw [hY₂]; exact hlt₁) (by rw [hY₂]; exact hY₁)
    (by rw [hs₂ sE (by decide) (by decide) (by decide) (by decide)]; exact he)
    (by rw [hs₂ sElen (by decide) (by decide) (by decide) (by decide)]; exact hlen)
    hL hL1 hL' (fun i hi => heb₂.rd i (by omega)) (fun i hi => heb₂.val i (by omega))
    (fun i hi => heb₂.out i (by omega))) fun t₃ ⟨hc₃, ⟨Y₃, hY₃, hYN₃, hYc₃⟩, f₃, k₃⟩ => ?_)
  have f₃' : Frm B (expPhaseRanges w) t₂.mem t₃.mem := f₃.mono fun r hr => List.mem_cons_of_mem _ hr
  have f₁₃ := f₁₂.trans f₃'
  -- `Y R⁻¹`.
  refine WP.mono (mmN_ok (o := aY) (a := aY) (b := aOne) hc₃.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hc₃.n hc₃.inv
    (by rw [f₁₃.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide), hone]; exact hN1))
    fun t ⟨hg₄, _, _, hlt₄, hm₄, ha₄, k₄⟩ => ⟨hg₄, ?_, f₁₃.trans (Frm.ep_of_arrays ha₄ (by simp)),
      (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)⟩
  rw [f₁₃.ep_wv (j := aOne) hn' (by decide) (by decide) (by decide) (by decide) (by decide), hone, Nat.mul_one,
    hY₃] at hm₄
  have hc : wv t.mem B (slot w aY) w % N = X ^ Spec.Rsa.os2ip eb % N := by
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₄, hYc₃]
  rw [← hc, Nat.mod_eq_of_lt hlt₄]

end VG.Proof.Bignum.X86_64
