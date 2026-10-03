import VerifiedGarbage.Proof.Bignum.X86_64.PubSetup

/-!
# `vg_rsa_public` on x86-64: `R² mod m`

`2^(b - 1)` for the bit length `b` of `m` (from the top bit of its top
word), doubled `64 - j + w` times to `2^w R mod m`, then squared six times
in Montgomery form: `R² mod m` (`r2_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

/-- One squaring of `[aR2] ≡ 2^E R`. -/
theorem sq_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N E : Nat} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N)
    (hn : wv t.mem B (slot w aN) w = N) (hinv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hlt : wv t.mem B (slot w aR2) w < N) (hc : wv t.mem B (slot w aR2) w % N = 2 ^ E * 2 ^ (64 * w) % N) :
    WP isa (mm aR2 aR2 aR2) t fun t' => Good t' B Z w minv ∧ wv t'.mem B (slot w aN) w = N ∧
      ((word t'.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem B (slot w aR2) w < N ∧ wv t'.mem B (slot w aR2) w % N = 2 ^ (2 * E) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
  refine WP.mono (mm_ok hg hZ hw hw' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hinv (by rw [hn]; exact hlt)) fun t' ⟨hg', hlt', hm, ha, k⟩ => ?_
  rw [hn] at hlt' hm
  refine ⟨hg', by rw [ha.wv_of_not_mem (by decide) (by decide) hn']; exact hn,
    by rw [ha.word0_of_not_mem (by decide) (by decide) hn' (by omega)]; exact hinv, hlt', ?_, ha, k⟩
  exact VG.Proof.Bignum.mont_sq hR hc hm

/-- `n + 1` squarings: `2^E R` becomes `2^(2^(n + 1) E) R`. -/
theorem sqs_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N E : Nat} (n : Nat)
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N)
    (hn : wv t.mem B (slot w aN) w = N) (hinv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (hlt : wv t.mem B (slot w aR2) w < N) (hc : wv t.mem B (slot w aR2) w % N = 2 ^ E * 2 ^ (64 * w) % N) :
    WP isa (seqs (List.replicate (n + 1) (mm aR2 aR2 aR2))) t fun t' => Good t' B Z w minv ∧
      wv t'.mem B (slot w aR2) w < N ∧
      wv t'.mem B (slot w aR2) w % N = 2 ^ (2 ^ (n + 1) * E) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aR2] t.mem t'.mem ∧ Keep mmRegs t t' := by
  induction n generalizing t E with
  | zero =>
    exact WP.mono (sq_ok hg hZ hw hw' hR hn hinv hlt hc) fun t' ⟨h1, _, _, h4, h5, h6, h7⟩ =>
      ⟨h1, h4, by rw [h5]; rfl, h6, h7⟩
  | succ n ih =>
    show WP isa (.seq (mm aR2 aR2 aR2) (seqs (List.replicate (n + 1) (mm aR2 aR2 aR2)))) t _
    refine WP.seq (WP.mono (sq_ok hg hZ hw hw' hR hn hinv hlt hc) fun t₁ ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ?_)
    refine WP.mono (ih h1 h2 h3 h4 h5) fun t' ⟨g1, g2, g3, g4, g5⟩ => ⟨g1, g2, ?_, h6.trans g4 |>.mono (by simp),
      (h7.trans g5).mono (by decide)⟩
    rw [g3, show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 from rfl, Nat.mul_assoc]

/-- The steps of `R² mod m`. -/
def r2Steps : List (Prog isa) := [
  .block [.mov .rax (.mem (ix .r10 .r12 (-8)))],
  topBit,
  .block [.store (hdr sCnt) .rcx, .mov .rcx (.reg .r12), .alu .sub .rcx (.imm 1)],
  setWord aR2 .rcx,
  .block [.mov .rcx (.mem (hdr sCnt)), .alu .add .rcx (.mem (hdr sW))],
  doubles aN aAcc aTmp aR2 sCnt,
  mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2, mm aR2 aR2 aR2]

/-- What `R² mod m` changes. -/
def r2Ranges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aR2, 8 * (w + 2)), (8 * sCnt, 8)]

/-- The start, `2^(b - 1)` for the bit length `b` of the odd `N`, is below
it. -/
theorem start_lt {N T L w : Nat} (hw : 2 ≤ w) (hodd : N % 2 = 1)
    (hT : N = N % 2 ^ (64 * (w - 1)) + 2 ^ (64 * (w - 1)) * T) (hL : 2 ^ L ≤ T) :
    2 ^ L * 2 ^ (64 * (w - 1)) < N := by
  have h1 : 2 ^ L * 2 ^ (64 * (w - 1)) ≤ 2 ^ (64 * (w - 1)) * T := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hL
  rcases Nat.lt_or_ge (2 ^ L * 2 ^ (64 * (w - 1))) N with h | h
  · exact h
  · exfalso
    have he : N = 2 ^ L * 2 ^ (64 * (w - 1)) := by omega
    have : 2 ^ L * 2 ^ (64 * (w - 1)) % 2 = 0 := by
      rw [show 64 * (w - 1) = (64 * (w - 1) - 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left]
    omega

theorem r2Ranges_arr (w : Nat) {j : Nat} (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    ∀ r ∈ r2Ranges w, slot w j + 8 * (w + 2) ≤ r.1 ∨ r.1 + r.2 ≤ slot w j := by
  have := hdr_lt_slot w j (show sCnt < 32 by decide)
  have s1 := slot_sep (w := w) h1
  have s2 := slot_sep (w := w) h2
  have s3 := slot_sep (w := w) h3
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> omega

theorem r2Ranges_hdr (w : Nat) {i : Nat} (hi : i < 32) (h : i ≠ sCnt) :
    ∀ r ∈ r2Ranges w, 8 * i + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * i := by
  have := hdr_lt_slot w aAcc hi
  have := hdr_lt_slot w aTmp hi
  have := hdr_lt_slot w aR2 hi
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> simp only [sCnt, sFn] at * <;> omega

theorem r2Ranges_le (w : Nat) : ∀ r ∈ r2Ranges w, r.1 + r.2 ≤ slot w 8 := by
  have := slot_le (w := w) (show aAcc < 8 by decide)
  have := slot_le (w := w) (show aTmp < 8 by decide)
  have := slot_le (w := w) (show aR2 < 8 by decide)
  have := hdr_lt_slot w 0 (show sCnt < 32 by decide)
  have := slot_le (w := w) (show 0 < 8 by decide)
  simp only [r2Ranges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> omega

theorem Frm.r2_wv {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (r2Ranges w) m m')
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    wv m' B (slot w j) w = wv m B (slot w j) w :=
  h.wv_eq (fun r hr => by have := r2Ranges_arr w h1 h2 h3 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem Frm.r2_word {B : Addr} {w : Nat} {m m' : Mem} (h : Frm B (r2Ranges w) m m')
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) (h1 : j ≠ aAcc) (h2 : j ≠ aTmp) (h3 : j ≠ aR2) :
    word m' B (slot w j) = word m B (slot w j) :=
  h.word_eq (fun r hr => by have := r2Ranges_arr w h1 h2 h3 r hr; omega)
    (by have := slot_le (w := w) hj; omega)

theorem pow_r2 {L w : Nat} (hL : L < 64) (hw : 1 ≤ w) :
    2 ^ (64 - L + w) * (2 ^ L * 2 ^ (64 * (w - 1))) = 2 ^ w * 2 ^ (64 * w) := by
  rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; omega

/-- `R² mod m`, for the odd `m` of `w ≥ 2` words, its top word not zero. -/
theorem r2_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N : Nat} (hg : Good s B Z w minv)
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw30 : w < 2 ^ 30) (hn : wv s.mem B (slot w aN) w = N)
    (hinv : ((word s.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0)
    (h12 : s.gpr .r12 = BitVec.ofNat 64 w) (h10 : s.gpr .r10 = off B (slot w aN)) (hodd : N % 2 = 1)
    (hlo : 2 ^ (64 * (w - 1)) ≤ N) :
    WP isa (seqs r2Steps) s fun t => Good t B Z w minv ∧
      wv t.mem B (slot w aR2) w < N ∧ wv t.mem B (slot w aR2) w % N = 2 ^ (64 * w) * 2 ^ (64 * w) % N ∧
      Frm B (r2Ranges w) s.mem t.mem ∧ Keep mmRegs s t := by
  have hw' : w < 2 ^ 31 := by omega
  have hs := hg.scr
  have hnw := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hR : Nat.Coprime (2 ^ (64 * w)) N := VG.Proof.Bignum.coprime_pow2 hodd _
  have hN0 : 0 < N := by omega
  -- The top word `T` of `N`.
  have hsl := slot_le (w := w) (show aN < 8 by decide)
  have hsplit : N = N % 2 ^ (64 * (w - 1)) +
      2 ^ (64 * (w - 1)) * (word s.mem B (slot w aN + 8 * (w - 1))).toNat := by
    have e : wv s.mem B (slot w aN) (w - 1 + 1) = N := by rw [Nat.sub_add_cancel (by omega : 1 ≤ w)]; exact hn
    rw [wv] at e
    have hlt := wv_lt s.mem B (slot w aN) (w - 1)
    rw [← e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hNlt : N < 2 ^ (64 * w) := hn ▸ wv_lt _ _ _ _
  generalize hT : (word s.mem B (slot w aN + 8 * (w - 1))).toNat = T at hsplit
  have hT0 : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h | h
    · rw [h, Nat.mul_zero, Nat.add_zero] at hsplit
      have := Nat.mod_lt N (Nat.two_pow_pos (64 * (w - 1))); omega
    · exact h
  have hT1 : T < 2 ^ 64 := hT ▸ BitVec.isLt _
  have hL : T.log2 < 64 := (Nat.log2_lt (by omega)).mpr hT1
  have hle := Nat.log2_self_le (n := T) (by omega)
  have hv0 := start_lt hw hodd hsplit hle
  unfold r2Steps
  -- The top word.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = BitVec.ofNat 64 T ∧ t.mem = s.mem) (by
    xrun [State.ea, ix, addrm8 h10 h12 (by omega), hs.ld (show slot w aN + 8 * (w - 1) + 8 ≤ Z by omega)]
    rw [← hT, BitVec.ofNat_toNat, BitVec.setWidth_eq]) rfl) fun t₁ ⟨⟨hax, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (topBit_ok hax hT0 hT1) fun t₂ ⟨hdx₂, hcx₂, hm₂, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hs₂ := hs.congr k12.2.2
  have hdi₂ : t₂.gpr .rdi = B := (k12.gpr (by decide)).trans hg.rdi
  have h12₂ : t₂.gpr .r12 = BitVec.ofNat 64 w := (k12.gpr (by decide)).trans h12
  have hm₂' : t₂.mem = s.mem := hm₂.trans hm₁
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (w - 1) ∧
      t.mem = s.mem.writeW (off B (8 * sCnt)) (BitVec.ofNat 64 (64 - T.log2))) (by
    xrun [State.ea, hdr, hdi₂, hdrOff, hs₂.st (d := 8 * sCnt) (by have := hdr_lt_slot w 0 (show sCnt < 32 by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega),
      hcx₂, h12₂, hm₂', ofNat64_pred (show 1 ≤ w by omega) (by omega)]) rfl) fun t₃ ⟨⟨hcx₃, hm₃⟩, k₃⟩ => ?_)
  have hs₃ := hs₂.congr k₃.2.2
  have hH₃ : Hdr t₃.mem B w minv := by rw [hm₃]; exact Hdr.store hg.hdr (by decide) (by decide) _
  have hdx₃ : t₃.gpr .rdx = BitVec.ofNat 64 (2 ^ T.log2) := (k₃.gpr (by decide)).trans hdx₂
  refine WP.seq (WP.mono (setWord_ok hs₃ ((k₃.gpr (by decide)).trans hdi₂) hH₃ hZ
    ((k₃.gpr (by decide)).trans h12₂) (by omega) hw' (o := aR2) (by decide) (ri := .rcx) (by decide)
    (i := w - 1) (by omega) hcx₃) fun t₄ ⟨hv₄, ho₄, k₄⟩ => ?_)
  rw [hdx₃, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hL)] at hv₄
  have hs₄ := hs₃.congr k₄.2.2
  have ha₄ : Arrays B w [aR2] t₃.mem t₄.mem :=
    Arrays.of_outside (List.mem_singleton_self _) ho₄ (Nat.le_refl _) (Nat.le_refl _)
  have hH₄ : Hdr t₄.mem B w minv := ha₄.hdr hH₃
  have hdi₄ : t₄.gpr .rdi = B := (k₄.gpr (by decide)).trans ((k₃.gpr (by decide)).trans hdi₂)
  have hcnt₄ : word t₄.mem B (8 * sCnt) = BitVec.ofNat 64 (64 - T.log2) := by
    rw [ha₄.hslot (by decide), hm₃, word_writeW_self]
  refine WP.seq (WP.mono (WP.keep [.rcx] (Q := fun t => t.gpr .rcx = BitVec.ofNat 64 (64 - T.log2 + w) ∧
      t.mem = t₄.mem) (by
    have h0 := hdr_lt_slot w 0 (show 31 < 32 by decide)
    have h0' := slot_le (w := w) (show 0 < 8 by decide)
    xrun [State.ea, hdr, hdi₄, hdrOff, hs₄.ld (d := 8 * sCnt) (by unfold sCnt sFn; omega),
      hs₄.ld (d := 8 * sW) (by unfold sW; omega),
      hcnt₄, hH₄.hw, ← BitVec.ofNat_add]) rfl) fun t₅ ⟨⟨hcx₅, hm₅⟩, k₅⟩ => ?_)
  have hs₅ := hs₄.congr k₅.2.2
  have hN₄ : wv t₄.mem B (slot w aN) w = N := by
    rw [ha₄.wv_of_not_mem (by decide) (by decide) hn', hm₃, hdrStore_wv _ _ _ (by decide) (by decide) hn']
    exact hn
  have hw0₄ : word t₄.mem B (slot w aN) = word s.mem B (slot w aN) := by
    rw [ha₄.word0_of_not_mem (by decide) (by decide) hn' (by omega), hm₃,
      hdrStore_word _ _ _ (by decide) (by decide) hn']
  refine WP.seq (WP.mono (doubles_ok hs₅ ((k₅.gpr (by decide)).trans hdi₄) (hm₅ ▸ hH₄) hZ hw hw'
    (mo := aN) (acc := aAcc) (tmp := aTmp) (o := aR2) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (sl := sCnt) (by decide) (by decide)
    (c := 64 - T.log2 + w) (by omega) (by omega) hcx₅ (by rw [hm₅, hv₄, hN₄]; exact hv0))
    fun t₆ ⟨hv₆, hf₆, hH₆, k₆⟩ => ?_)
  rw [hm₅, hv₄, hN₄, pow_r2 hL (by omega)] at hv₆
  have hf₆' : Frm B (r2Ranges w) t₅.mem t₆.mem := hf₆
  have hg₆ : Good t₆ B Z w minv := ⟨hs₅.congr k₆.2.2, (k₆.gpr (by decide)).trans ((k₅.gpr (by decide)).trans hdi₄),
    hH₆⟩
  show WP isa (seqs (List.replicate (5 + 1) (mm aR2 aR2 aR2))) t₆ _
  refine WP.mono (sqs_ok 5 hg₆ hZ hw hw' hR (E := w)
    (by rw [hf₆'.r2_wv hn' (by decide) (by decide) (by decide) (by decide), hm₅]; exact hN₄)
    (by rw [hf₆'.r2_word hn' (by decide) (by decide) (by decide) (by decide), hm₅, hw0₄]; exact hinv)
    (by rw [hv₆]; exact Nat.mod_lt _ hN0) (by rw [hv₆, Nat.mod_mod]))
    fun t ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, by rw [h3]; congr 2, ?_,
      ((((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).trans k₆).trans h5).mono (by decide)⟩
  have f₃ : Frm B (r2Ranges w) s.mem t₃.mem := by
    rw [hm₃]; exact Frm.of_outside (writeW_outside _ B _ (by have := hdr_lt_slot w 0 (show sCnt < 32 by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega)) (by simp [r2Ranges])
  exact (((f₃.trans (Frm.of_arrays ha₄ (by simp [r2Ranges]))).trans (by rw [hm₅]; exact Frm.refl _ _ _)).trans
    hf₆').trans (Frm.of_arrays h4 (by simp [r2Ranges]))

end VG.Proof.Bignum.X86_64
