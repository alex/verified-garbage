import VerifiedGarbage.Proof.Bignum.X86_64.Exp
import VerifiedGarbage.Proof.Bignum.X86_64.Copy

/-!
# `vg_rsa_public_precomputed` on x86-64: the exponentiation

The exponentiation of `vg_rsa_public_precomputed` starts at the first set bit
of `e`: until then `Y` is not used (`YSt`); at that bit `Y := X`, and after
it each bit squares `Y` and multiplies it by `X` if set (`pExpBit_ok`, over
the bits and bytes of `e` in `pExpLoop_ok`). `finish` leaves `x^e mod N`
(`pFinish_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Precomputed
open VG.Proof.MlKem.X86_64

/-- What a bit of the exponentiation changes: also whether it started. -/
def pBitRanges (w : Nat) : List (Nat × Nat) := (8 * sStarted, 8) :: bitRanges w

/-- What `start` changes. -/
def startRanges (w : Nat) : List (Nat × Nat) := [(slot w aY, 8 * (w + 2)), (8 * sStarted, 8)]

theorem startRanges_sub (w : Nat) : ∀ r ∈ startRanges w, r ∈ pBitRanges w := by
  simp [startRanges, pBitRanges, bitRanges]

/-- `Y` after the prefix `E` of `e`: unused, and not started, while `E = 0`;
started, and `x^E R` modulo `N`, after. -/
def YSt (m : Mem) (B : Addr) (w N x E : Nat) : Prop :=
  (E = 0 ∧ word m B (8 * sStarted) = 0) ∨
    (E ≠ 0 ∧ word m B (8 * sStarted) = 1 ∧
      ∃ Y, wv m B (slot w aY) w = Y ∧ Y < N ∧ Y % N = x ^ E * 2 ^ (64 * w) % N)

theorem YSt.started {m : Mem} {B : Addr} {w N x E : Nat} (h : YSt m B w N x E) :
    word m B (8 * sStarted) = if E = 0 then 0 else 1 := by
  rcases h with ⟨h0, hs⟩ | ⟨h0, hs, -⟩
  · rw [hs]; simp [h0]
  · rw [hs]; simp [h0]

theorem started_test (E : Nat) :
    ((if E = 0 then (0 : BitVec 64) else 1) &&& (if E = 0 then (0 : BitVec 64) else 1) == 0) =
      decide (E = 0) := by
  by_cases h : E = 0 <;> simp [h]

/-- Whether the exponentiation started, into ZF. -/
theorem startedTest_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N x E : Nat}
    (hg : Good t B Z w minv) (hZ : slot w 8 ≤ Z) (hy : YSt t.mem B w N x E) :
    WP isa (.block startedTest) t fun t' => t'.zf = some (decide (E = 0)) ∧ t'.mem = t.mem ∧ Keep [.rax] t t' := by
  have hn := hg.scr.nowrap
  have hl : InRegions (t.rd ++ t.wr) (off B (8 * sStarted)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (E = 0)) ∧ t'.mem = t.mem) (by
    unfold startedTest
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hy.started, started_test]) rfl)
    fun t' ⟨⟨hz, hm⟩, k⟩ => ⟨hz, hm, k⟩

/-- `start`: `Y := X`, and the exponentiation started. -/
theorem start_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) :
    WP isa start t fun t' => ExpCtx t' B Z w minv N X ∧ wv t'.mem B (slot w aY) w = X ∧
      word t'.mem B (8 * sStarted) = 1 ∧ Frm B (startRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hs := hc.good.scr
  have hn := hs.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hX := slot_le (w := w) (show aXm < 8 by decide)
  have hY := slot_le (w := w) (show aY < 8 by decide)
  have hXY : slot w aXm + 8 * (w + 2) ≤ slot w aY := by unfold slot aXm aY; omega
  have hYs := hdr_lt_slot w aY (show sStarted < 32 by decide)
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hs.ld (by have := hdr_lt_slot w 8 hi; omega)
  unfold start
  refine WP.seq (WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 w ∧
      t₁.gpr .rsi = off B (slot w aXm) ∧ t₁.gpr .rbx = off B (slot w aY) ∧ t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sW (by decide), hl (sArr aXm) (by decide),
      hl (sArr aY) (by decide), hc.good.hdr.hw, hc.good.hdr.harr aXm (by decide),
      hc.good.hdr.harr aY (by decide)]) rfl)
    fun t₁ ⟨⟨h12, hsi, hbx, hm₁⟩, k₁⟩ => ?_)
  refine WP.seq (WP.mono (copyWords_ok hsi hbx h12 hw hw' (by omega)
    (fun j hj => by rw [k₁.2.1, k₁.2.2]; exact hs.ld (by omega))
    (fun j hj => by rw [k₁.2.2]; exact hs.st (by omega))
    (fun j hj b hb => Or.inl (by rw [ofs_off B (d := slot w aXm + 8 * j) (i := b) (by omega)]; omega)))
    fun t₂ ⟨hv₂, _, ho₂, k₂⟩ => ?_)
  rw [hm₁, hc.x] at hv₂
  rw [hm₁] at ho₂
  have k12 := k₁.trans k₂
  have ha₂ : Arrays B w [aAcc, aTmp, aY] t.mem t₂.mem :=
    Arrays.of_outside (j := aY) (by simp) ho₂ (Nat.le_refl _) (by omega)
  have hc₂ : ExpCtx t₂ B Z w minv N X := hc.of_arrays ⟨hs.congr k12.2.2,
    (k12.gpr (by decide)).trans hc.good.rdi, ha₂.hdr hc.good.hdr⟩ hZ hw ha₂
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (off B (8 * sStarted))
      (BitVec.setWidth 64 (1 : BitVec 32))) (by
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff,
      hc₂.good.scr.st (d := 8 * sStarted) (by have := hdr_lt_slot w 8 (show sStarted < 32 by decide); omega)])
    rfl) fun t' ⟨hm', k'⟩ => ?_
  refine ⟨ExpCtx.store hc₂ hZ (i := sStarted) (by decide) (by decide) hm' k'.2.2
    ((k'.gpr (by decide)).trans hc₂.good.rdi), ?_, by rw [hm', word_writeW_self]; rfl, ?_,
    (k12.trans k').mono (by decide)⟩
  · rw [hm', hdrStore_wv (i := sStarted) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hv₂
  · rw [hm']
    exact (Frm.of_outside (ho₂.mono (o' := slot w aY) (n' := 8 * (w + 2)) (Nat.le_refl _) (by omega))
      (by simp [startRanges])).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * sStarted) (by omega)) (by simp [startRanges]))

/-- `YSt` in memory with the same `Y` and the same flag. -/
theorem YSt.congr {m m' : Mem} {B : Addr} {w N x E : Nat} (h : YSt m B w N x E)
    (hs : word m' B (8 * sStarted) = word m B (8 * sStarted)) (hy : wv m' B (slot w aY) w = wv m B (slot w aY) w) :
    YSt m' B w N x E := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1, Y, h2, h3, h4⟩
  · exact .inl ⟨h0, hs.trans h1⟩
  · exact .inr ⟨h0, hs.trans h1, Y, hy.trans h2, h3, h4⟩

theorem ExpCtx.mem {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hm : t'.mem = t.mem) {regs : List Reg} (k : Keep regs t t')
    (hr : .rdi ∉ regs) : ExpCtx t' B Z w minv N X :=
  ⟨⟨hc.good.scr.congr k.2.2, (k.gpr hr).trans hc.good.rdi, hm ▸ hc.good.hdr⟩, hm ▸ hc.n, hm ▸ hc.inv, hm ▸ hc.x⟩

theorem pBitRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ sV) (h2 : k ≠ sBit) (h3 : k ≠ sStarted) :
    ∀ r ∈ pBitRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [sStarted, sFn] at *; omega
  · exact bitRanges_hdr w hk h1 h2 r hr

/-- `Y := Y²` once started. -/
theorem pSq_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hy : YSt t.mem B w N x E) (hz : t.zf = some (decide (E = 0))) :
    WP isa (.ite .ne (mm aY aY aY) (.block [])) t fun t' => ExpCtx t' B Z w minv N X ∧
      YSt t'.mem B w N x (2 * E) ∧ Arrays B w [aAcc, aTmp, aY] t.mem t'.mem ∧ Keep mmRegs t t' := by
  rcases hy with ⟨h0, hs0⟩ | ⟨h0, hs1, Y, hY, hYN, hYc⟩
  · refine WP.ite false (by simp [eval, hz, h0]) (by simp) (fun _ => WP.block_nil ⟨hc, ?_,
      fun _ _ => rfl, Keep.refl _ _⟩)
    exact .inl ⟨by omega, hs0⟩
  · refine WP.ite true (by simp [eval, hz, h0]) (fun _ => ?_) (by simp)
    refine WP.mono (mm_ok (o := aY) (a := aY) (b := aY) hc.good hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv
      (by rw [hc.n, hY]; exact hYN)) fun t₂ ⟨hg₂, hlt₂, hmm₂, ha₂, k₂⟩ => ?_
    rw [hc.n] at hlt₂
    rw [hc.n, hY] at hmm₂
    exact ⟨hc.of_arrays hg₂ hZ (by omega) ha₂, .inr ⟨by omega, by rw [ha₂.hslot (by decide)]; exact hs1,
      _, rfl, hlt₂, VG.Proof.Bignum.mont_sq hR hYc hmm₂⟩, ha₂, k₂⟩

/-- If the bit is set, `Y := Y X` once started, or `Y := X` and started. -/
theorem pMul_ok {t₃ : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E V : Nat}
    (hc₃ : ExpCtx t₃ B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hy₃ : YSt t₃.mem B w N x (2 * E)) (hz₃ : t₃.zf = some (decide (V / 128 % 2 = 0))) :
    WP isa (.ite .ne (.seq (.block startedTest) (.ite .ne (mm aY aY aXm) start)) (.block [])) t₃
      fun t₄ => ExpCtx t₄ B Z w minv N X ∧ YSt t₄.mem B w N x (2 * E + V / 128 % 2) ∧
        Frm B (pBitRanges w) t₃.mem t₄.mem ∧ (∀ k < 32, k ≠ sStarted → word t₄.mem B (8 * k) = word t₃.mem B (8 * k)) ∧
        Keep mmRegs t₃ t₄ := by
  have hn := hc₃.good.scr.nowrap
  have h8 : 256 ≤ slot w 0 := by unfold slot hdrBytes; omega
  by_cases hbit : V / 128 % 2 = 0
  · refine WP.ite false (by simp [eval, hz₃, hbit]) (by simp) (fun _ => WP.block_nil ⟨hc₃, ?_,
      Frm.refl _ _ _, fun _ _ _ => rfl, Keep.refl _ _⟩)
    rw [hbit, Nat.add_zero]; exact hy₃
  · refine WP.ite true (by simp [eval, hz₃, hbit]) (fun _ => ?_) (by simp)
    rw [show V / 128 % 2 = 1 by omega]
    refine WP.seq (WP.mono (startedTest_ok hc₃.good hZ hy₃) fun t₄ ⟨hz₄, hm₄, k₄⟩ => ?_)
    have hc₄ := hc₃.mem hm₄ k₄ (by decide)
    rcases hy₃ with ⟨h0, hs0⟩ | ⟨h0, hs1, Y, hY, hYN, hYc⟩
    · refine WP.ite false (by simp [eval, hz₄, h0]) (by simp) (fun _ => ?_)
      refine WP.mono (start_ok hc₄ hZ (by omega) hw') fun t₅ ⟨hc₅, hv₅, hs₅, hf₅, k₅⟩ => ?_
      refine ⟨hc₅, .inr ⟨by omega, hs₅, X, hv₅, hXN, by rw [show 2 * E + 1 = 1 by omega, Nat.pow_one]; exact hXc⟩,
        by rw [← hm₄]; exact hf₅.mono (startRanges_sub w), fun k hk hk' => ?_, (k₄.trans k₅).mono (by decide)⟩
      rw [hf₅.word_eq (fun r hr => by
        simp only [startRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
        have := hdr_lt_slot w aY hk
        rcases hr with rfl | rfl
        · omega
        · simp only [sStarted, sFn] at hk' ⊢; omega) (by omega), hm₄]
    · refine WP.ite true (by simp [eval, hz₄, h0]) (fun _ => ?_) (by simp)
      refine WP.mono (mm_ok (o := aY) (a := aY) (b := aXm) hc₄.good hZ hw hw' (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hc₄.inv
        (by rw [hc₄.x, hc₄.n]; exact hXN)) fun t₅ ⟨hg₅, hlt₅, hmm₅, ha₅, k₅⟩ => ?_
      rw [hc₄.n] at hlt₅
      rw [hc₄.n, hc₄.x, hm₄, hY] at hmm₅
      refine ⟨hc₄.of_arrays hg₅ hZ (by omega) ha₅, .inr ⟨by omega, by rw [ha₅.hslot (by decide), hm₄]; exact hs1,
        _, rfl, hlt₅, VG.Proof.Bignum.mont_mulx hR hYc hXc hmm₅⟩,
        by rw [← hm₄]; exact Frm.of_arrays ha₅ (by simp [pBitRanges, bitRanges]),
        fun k hk _ => by rw [ha₅.hslot hk, hm₄], (k₄.trans k₅).mono (by decide)⟩

/-- One bit of `e`: `YSt` for the prefix `E` becomes `YSt` for `2 E + bit`,
for the bit at the top of the byte `V / 128 mod 2`; `V` doubles and the bit
count `b` drops. -/
theorem pExpBit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E V b : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hy : YSt t.mem B w N x E)
    (hV : word t.mem B (8 * sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 62)
    (hb : word t.mem B (8 * sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa Precomputed.expBit t fun t' => ExpCtx t' B Z w minv N X ∧ YSt t'.mem B w N x (2 * E + V / 128 % 2) ∧
      word t'.mem B (8 * sV) = BitVec.ofNat 64 (V + V) ∧ word t'.mem B (8 * sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm B (pBitRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have eV : sV = 25 := rfl
  have eB : sBit = 24 := rfl
  have eS : sStarted = 27 := rfl
  have h8 : 256 ≤ slot w 0 := by unfold slot hdrBytes; omega
  unfold Precomputed.expBit
  -- Whether started.
  refine WP.seq (WP.mono (startedTest_ok hc.good hZ hy) fun t₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  have hc₁ := hc.mem hm₁ k₁ (by decide)
  -- `Y := Y²` if started.
  refine WP.seq (WP.mono (pSq_ok (x := x) hc₁ hZ hw hw' hR (by rw [hm₁]; exact hy) hz₁) fun t₂ ⟨hc₂, hy₂, ha₂, k₂⟩ => ?_)
  have hV₂ : word t₂.mem B (8 * sV) = BitVec.ofNat 64 V := by rw [ha₂.hslot (by decide), hm₁]; exact hV
  have hb₂ : word t₂.mem B (8 * sBit) = BitVec.ofNat 64 b := by rw [ha₂.hslot (by decide), hm₁]; exact hb
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- The bit, into ZF.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t₃ => t₃.zf = some (decide (V / 128 % 2 = 0)) ∧
      t₃.mem = t₂.mem) (by
    unfold bitTest
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hl₂ sV (by decide), hV₂, bit7 V (by omega)]) rfl)
    fun t₃ ⟨⟨hz₃, hm₃⟩, k₃⟩ => ?_)
  have hc₃ := hc₂.mem hm₃ k₃ (by decide)
  have hy₃ : YSt t₃.mem B w N x (2 * E) := by rw [hm₃]; exact hy₂
  -- If the bit is set: `Y := Y X` if started, `Y := X` and started if not.
  refine WP.seq (WP.mono (pMul_ok hc₃ hZ hw hw' hR hXN hXc hy₃ hz₃) fun t₄ ⟨hc₄, hy₄, hf₄, hh₄, k₄⟩ => ?_)
  -- The next bit.
  have hV₄ : word t₄.mem B (8 * sV) = BitVec.ofNat 64 V := by
    rw [hh₄ sV (by decide) (by decide), hm₃]; exact hV₂
  have hb₄ : word t₄.mem B (8 * sBit) = BitVec.ofNat 64 b := by
    rw [hh₄ sBit (by decide) (by decide), hm₃]; exact hb₂
  have hl₄ : ∀ i < 32, InRegions (t₄.rd ++ t₄.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₄.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₄ : ∀ i < 32, InRegions t₄.wr (off B (8 * i)) 8 := fun i hi =>
    hc₄.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hV₄' : (t₄.mem.writeW (off B (8 * sV)) (BitVec.ofNat 64 (V + V))).readW (off B (8 * sBit)) 64 =
      BitVec.ofNat 64 b := by
    rw [← hb₄]; exact (writeW_outside _ B _ (by omega)).word (by unfold sV sBit sFn; omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t₄.mem.writeW (off B (8 * sV))
      (BitVec.ofNat 64 (V + V))).writeW (off B (8 * sBit)) (BitVec.ofNat 64 (b - 1)) ∧
      t'.zf = some (decide (b - 1 = 0))) (by
    unfold bitNext
    xrun [State.ea, hdr, hc₄.good.rdi, hdrOff, hl₄ sV (by decide), hs₄ sV (by decide), hV₄, hV₄',
      hs₄ sBit (by decide), hl₄ sBit (by decide), ← BitVec.ofNat_add,
      ofNat64_pred hb1 (by omega), ofNat64_beq_zero (show b - 1 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ?_
  have o1 := writeW_outside t₄.mem B (BitVec.ofNat 64 (V + V)) (d := 8 * sV) (by unfold sV sFn; omega)
  have o2 := writeW_outside (t₄.mem.writeW (off B (8 * sV)) (BitVec.ofNat 64 (V + V))) B
    (BitVec.ofNat 64 (b - 1)) (d := 8 * sBit) (by omega)
  have hkeep : ∀ j < 8, wv t'.mem B (slot w j) w = wv t₄.mem B (slot w j) w := fun j hj => by
    rw [hm', o2.wv (by have := hdr_lt_slot w j (show sBit < 32 by decide); omega)
      (by have := slot_le (w := w) hj; omega),
      o1.wv (by have := hdr_lt_slot w j (show sV < 32 by decide); omega)
      (by have := slot_le (w := w) hj; omega)]
  have hw0 : word t'.mem B (slot w aN) = word t₄.mem B (slot w aN) := by
    have := slot_le (w := w) (show aN < 8 by decide)
    rw [hm', o2.word (by have := hdr_lt_slot w aN (show sBit < 32 by decide); omega) (by omega),
      o1.word (by have := hdr_lt_slot w aN (show sV < 32 by decide); omega) (by omega)]
  have hst' : word t'.mem B (8 * sStarted) = word t₄.mem B (8 * sStarted) := by
    rw [hm', hdrStore_hdr (i := sBit) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sV) _ _ _ (by decide) (by decide) (by decide)]
  have hgood : Good t' B Z w minv := ⟨hc₄.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hc₄.good.rdi,
    by rw [hm']; exact Hdr.store (Hdr.store hc₄.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  refine ⟨⟨hgood, by rw [hkeep aN (by decide)]; exact hc₄.n, by rw [hw0]; exact hc₄.inv,
    by rw [hkeep aXm (by decide)]; exact hc₄.x⟩, YSt.congr hy₄ hst' (hkeep aY (by decide)), ?_, ?_, hz', ?_,
    ((((k₁.trans k₂).trans k₃).trans k₄).trans k').mono (by decide)⟩
  · rw [hm', o2.word (by unfold sV sBit sFn; omega) (by omega), word_writeW_self]
  · rw [hm', word_writeW_self]
  · rw [hm']
    exact ((((by rw [hm₁]; exact Frm.refl _ _ _ : Frm B (pBitRanges w) t.mem t₁.mem).trans
      (Frm.of_arrays ha₂ (by simp [pBitRanges, bitRanges]))).trans (by rw [hm₃]; exact Frm.refl _ _ _)).trans hf₄).trans
      ((Frm.of_outside o1 (by simp [pBitRanges, bitRanges])).trans (Frm.of_outside o2 (by simp [pBitRanges, bitRanges])))

/-! ## The bits of a byte -/

/-- After `j` bits of the byte `v` from `t₀`, after the prefix `E`. -/
structure PBitInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x E v : Nat) (j : Nat)
    (t : State) : Prop where
  ctx : ExpCtx t B Z w minv N X
  y : YSt t.mem B w N x (E * 2 ^ j + v / 2 ^ (8 - j))
  v : word t.mem B (8 * sV) = BitVec.ofNat 64 (v * 2 ^ j)
  b : word t.mem B (8 * sBit) = BitVec.ofNat 64 (8 - j)
  frm : Frm B (pBitRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Bit `j` of the byte `v`. -/
theorem pBitStep_ok {t s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) {j : Nat} (hj : j < 8) (hI : PBitInv t B Z w minv N X x E v j s) :
    WP isa Precomputed.expBit s fun s' => s'.zf = some (decide (j + 1 = 8)) ∧
      PBitInv t B Z w minv N X x E v (j + 1) s' := by
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (pExpBit_ok hI.ctx hZ hw hw' hR hXN hXc hI.y hI.v
    (by have := Nat.mul_le_mul_left v hp; omega) hI.b (by omega) (by omega))
    fun s' ⟨hc', hy', hV', hb', hz', hfr', k'⟩ => ⟨?_, ⟨hc', ?_, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by simp [mmRegs])⟩⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  · rwa [show 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) by
        rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]] at hy'
  · rw [hV', ← Nat.two_mul, Nat.pow_succ]; congr 1; rw [Nat.mul_comm, Nat.mul_assoc]
  · rw [hb']; congr 1

theorem pBits_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) (h0 : PBitInv t B Z w minv N X x E v 0 t) :
    WP isa (.loop Precomputed.expBit .ne) t (PBitInv t B Z w minv N X x E v 8) :=
  wp_upto (a := 0) (N := 8) (by decide) (PBitInv t B Z w minv N X x E v)
    (fun _ _ hj _ hI => pBitStep_ok hZ hw hw' hR hXN hXc hv hj hI) (fun _ h => h) h0

/-! ## The bytes -/

/-- What the exponentiation changes: also the byte index. -/
def pExpRanges (w : Nat) : List (Nat × Nat) := (8 * sI, 8) :: pBitRanges w

/-- After `i` bytes of `e` (`L` bytes `eb` at `ep`) from `t₀`. -/
structure PByteInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x : Nat) (ep : Addr)
    (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : ExpCtx t B Z w minv N X
  y : YSt t.mem B w N x (pre eb i)
  idx : word t.mem B (8 * sI) = BitVec.ofNat 64 i
  e : word t.mem B (8 * sE) = ep
  len : word t.mem B (8 * sElen) = BitVec.ofNat 64 L
  frm : Frm B (pExpRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem pExpRanges_le (w : Nat) : ∀ r ∈ pExpRanges w, r.1 + r.2 ≤ slot w 8 := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot w 0 (i := sI) (by decide); have := slot_le (w := w) (show 0 < 8 by decide); omega
  rcases List.mem_cons.mp hr with rfl | hr
  · have := hdr_lt_slot w 0 (i := sStarted) (by decide); have := slot_le (w := w) (show 0 < 8 by decide)
    omega
  · exact expRanges_le w r (List.mem_cons_of_mem _ hr)

theorem pExpRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ sI) (h1 : k ≠ sV) (h2 : k ≠ sBit)
    (h3 : k ≠ sStarted) : ∀ r ∈ pExpRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [sI, sFn] at *; omega
  · exact pBitRanges_hdr w hk h1 h2 h3 r hr

theorem pBitRanges_sub (w : Nat) : ∀ r ∈ pBitRanges w, r ∈ pExpRanges w :=
  fun _ hr => List.mem_cons_of_mem _ hr

/-- `byteHead`'s loads: `e` and the byte index. -/
theorem pByteHead1_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hI : PByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ PByteInv t₀ B Z w minv N X x ep L eb i t₁ := by
  have hc := hI.ctx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sE (by decide), hl sI (by decide), hI.e, hI.idx]) rfl)
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  exact ⟨hc.mem hm k (by decide), hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e, hm ▸ hI.len, hm ▸ hI.frm,
    (hI.keep.trans k).mono (by decide)⟩

/-- `byteHead`'s byte of `e` into `sV`, and the bit count 8: the start of the
bits. -/
theorem pByteHead2_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i))
    (hI : PByteInv t₀ B Z w minv N X x ep L eb i t) (hax : t.gpr .rax = ep)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr sV) .rax,
      .mov32 .rax (.imm 8), .store (hdr sBit) .rax]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (off B (8 * sV)) ((eb[i]'(by omega)).setWidth 64)).writeW (off B (8 * sBit))
        (BitVec.setWidth 64 (8 : BitVec 32)) ∧ Keep [.rax] t t₁ ∧
      PBitInv t₁ B Z w minv N X x (pre eb i) (eb[i]'(by omega)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hs : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := pExpRanges_le w r hr; have := hout i hi; omega)]
    exact hbytes i hi
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off B (8 * sV))
      ((eb[i]'(by omega)).setWidth 64)).writeW (off B (8 * sBit)) (BitVec.setWidth 64 (8 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hax, hcx, byteRead, hrdi, hbi, hs sV (by decide),
      hs sBit (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ⟨hm₁, k₁, ?_⟩
  have hc₁ : ExpCtx t₁ B Z w minv N X := ⟨⟨hc.good.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hc.good.rdi,
    by rw [hm₁]; exact Hdr.store (Hdr.store hc.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    by rw [hm₁, hdrStore_wv (i := sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.n,
    by rw [hm₁, hdrStore_word (i := sBit) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_word (i := sV) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.inv,
    by rw [hm₁, hdrStore_wv (i := sBit) (j := aXm) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sV) (j := aXm) _ _ _ (by decide) (by decide) hn']; exact hc.x⟩
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine ⟨hc₁, ?_, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 2 ^ 8 from hv), Nat.add_zero]
    exact YSt.congr hI.y (by rw [hm₁, hdrStore_hdr (i := sBit) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sV) _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm₁, hdrStore_wv (i := sBit) (j := aY) _ _ _ (by decide) (by decide) hn',
        hdrStore_wv (i := sV) (j := aY) _ _ _ (by decide) (by decide) hn'])
  · rw [hm₁, hdrStore_hdr (i := sBit) (k := sV) _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self, setWidth_byte]
  · rw [hm₁, word_writeW_self]; rfl

/-- One byte of `e`: its eight bits, then the next byte. -/
theorem pByte_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr} {L : Nat}
    {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i))
    (hI : PByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.seq (.block byteHead) (.seq (.loop Precomputed.expBit .ne) (.block byteNext))) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ PByteInv t₀ B Z w minv N X x ep L eb (i + 1) t' := by
  have hn := hI.ctx.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  rw [byteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (pByteHead1_ok hZ hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (pByteHead2_ok hZ hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine WP.seq (WP.mono (pBits_ok hZ hw hw' hR hXN hXc hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₂ : ∀ i < 32, InRegions t₂.wr (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hh₂ : ∀ k < 32, k ≠ sV → k ≠ sBit → k ≠ sStarted → word t₂.mem B (8 * k) = word tₐ.mem B (8 * k) :=
    fun k hk h1 h2 h3 => by
      rw [h₂.frm.word_eq (pBitRanges_hdr w hk h1 h2 h3) (by omega), hm₁,
        hdrStore_hdr (i := sBit) _ _ _ (by decide) hk (Ne.symm h2),
        hdrStore_hdr (i := sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ sI (by decide) (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ sE (by decide) (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ sElen (by decide) (by decide) (by decide) (by decide)).trans hIₐ.len
  have hlen₂' : (t₂.mem.writeW (off B (8 * sI)) (BitVec.ofNat 64 (i + 1))).readW (off B (8 * sElen)) 64 =
      BitVec.ofNat 64 L := by
    rw [← hlen₂]; exact hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = t₂.mem.writeW (off B (8 * sI))
      (BitVec.ofNat 64 (i + 1)) ∧ t'.zf = some (decide (i + 1 = L))) (by
    unfold byteNext
    xrun [State.ea, hdr, hc₂.good.rdi, hdrOff, hl₂ sI (by decide), hs₂ sI (by decide), hidx₂,
      ofNat_add_one, hl₂ sElen (by decide), hlen₂', ofNat_sub_beq (show i + 1 < 2 ^ 64 by omega)
      (show L < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ⟨hz', ?_⟩
  refine ⟨ExpCtx.store hc₂ hZ (i := sI) (by decide) (by decide) hm' k'.2.2 ((k'.gpr (by decide)).trans
    hc₂.good.rdi), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hy := h₂.y
    rw [show pre eb i * 2 ^ 8 + (eb[i]'(by omega)).toNat / 2 ^ (8 - 8) = pre eb (i + 1) by
      rw [pre_succ eb (by omega)]; omega] at hy
    exact YSt.congr hy (by rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)])
      (by rw [hm', hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hn'])
  · rw [hm', word_writeW_self]
  · rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm B (pExpRanges w) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (writeW_outside tₐ.mem B _ (d := 8 * sV) (by unfold sV sFn; omega))
        (by simp [pExpRanges, pBitRanges, bitRanges])).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * sBit) (by unfold sBit sFn; omega))
          (by simp [pExpRanges, pBitRanges, bitRanges]))
    have f₃ : Frm B (pExpRanges w) t₂.mem t'.mem := by
      rw [hm']; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * sI) (by unfold sI sFn; omega))
        (by simp [pExpRanges])
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (pBitRanges_sub w))).trans f₃
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-- The loop's start: byte index 0, not started. -/
theorem pExpInit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z)
    (he : word t.mem B (8 * sE) = ep) (hlen : word t.mem B (8 * sElen) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (hdr sI) .rax, .store (hdr sStarted) .rax]) t
      (PByteInv t B Z w minv N X x ep L eb 0) := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hst : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = (t.mem.writeW (off B (8 * sI))
      (BitVec.setWidth 64 (0 : BitVec 32))).writeW (off B (8 * sStarted)) (BitVec.setWidth 64 (0 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hst sI (by decide), hst sStarted (by decide)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  have hc₁ : ExpCtx t₁ B Z w minv N X := ⟨⟨hc.good.scr.congr k₁.2.2, (k₁.gpr (by decide)).trans hc.good.rdi,
    by rw [hm₁]; exact Hdr.store (Hdr.store hc.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩,
    by rw [hm₁, hdrStore_wv (i := sStarted) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sI) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.n,
    by rw [hm₁, hdrStore_word (i := sStarted) (j := aN) _ _ _ (by decide) (by decide) hn',
      hdrStore_word (i := sI) (j := aN) _ _ _ (by decide) (by decide) hn']; exact hc.inv,
    by rw [hm₁, hdrStore_wv (i := sStarted) (j := aXm) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sI) (j := aXm) _ _ _ (by decide) (by decide) hn']; exact hc.x⟩
  refine ⟨hc₁, .inl ⟨pre_zero eb, by rw [hm₁, word_writeW_self]; rfl⟩, ?_, ?_, ?_, ?_, k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide), word_writeW_self]; rfl
  · rw [hm₁, hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact he
  · rw [hm₁, hdrStore_hdr (i := sStarted) _ _ _ (by decide) (by decide) (by decide),
      hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen
  · rw [hm₁]
    exact (Frm.of_outside (writeW_outside _ B _ (d := 8 * sI) (by unfold sI sFn; omega)) (by simp [pExpRanges])).trans
      (Frm.of_outside (writeW_outside _ B _ (d := 8 * sStarted) (by unfold sStarted sFn; omega))
        (by simp [pExpRanges, pBitRanges]))

/-- The exponentiation: `YSt` for `e`, the `L` bytes `eb` at `ep`, outside the
working space. -/
theorem pExpLoop_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N)
    (hXc : X % N = x * 2 ^ (64 * w) % N)
    (he : word t.mem B (8 * sE) = ep) (hlen : word t.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i)) :
    WP isa Precomputed.expLoop t fun t' => ExpCtx t' B Z w minv N X ∧
      YSt t'.mem B w N x (Spec.Rsa.os2ip eb) ∧ Frm B (pExpRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  unfold Precomputed.expLoop
  refine WP.seq (WP.mono (pExpInit_ok (x := x) (eb := eb) hc hZ he hlen) fun t₁ h₁ => ?_)
  refine wp_upto (a := 0) (N := L) (by omega) (PByteInv t B Z w minv N X x ep L eb)
    (fun i _ hi s hI => pByte_ok hZ hw hw' hR hXN hXc hL hL' hi hrd hbytes hout hI)
    (fun s hI => ?_) h₁
  exact ⟨hI.ctx, by rw [← pre_len, hL]; exact hI.y, hI.frm, hI.keep⟩

/-! ## The result -/

/-- What `finish` changes. -/
def finRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2))]

/-- `finish`: `Y R⁻¹`, which is `x^E mod N`, or 1 if `E = 0`. -/
theorem pFinish_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hN1 : 1 < N) (hone : wv t.mem B (slot w aOne) w = 1)
    (hy : YSt t.mem B w N x E) :
    WP isa finish t fun t' => Good t' B Z w minv ∧ wv t'.mem B (slot w aY) w = x ^ E % N ∧
      Frm B (finRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  unfold finish
  refine WP.seq (WP.mono (startedTest_ok hc.good hZ hy) fun t₁ ⟨hz₁, hm₁, k₁⟩ => ?_)
  have hc₁ := hc.mem hm₁ k₁ (by decide)
  rcases hy with ⟨h0, -⟩ | ⟨h0, -, Y, hY, hYN, hYc⟩
  · refine WP.ite false (by simp [eval, hz₁, h0]) (by simp) (fun _ => ?_)
    have hl : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off B (8 * i)) 8 := fun i hi =>
      hc₁.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
    refine WP.seq (WP.mono (WP.keep [.r12, .rdx, .rcx] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 w ∧
        t₂.gpr .rdx = 1 ∧ t₂.gpr .rcx = BitVec.ofNat 64 0 ∧ t₂.mem = t₁.mem) (by
      xrun [State.ea, hdr, hc₁.good.rdi, hdrOff, hl sW (by decide), hc₁.good.hdr.hw]) rfl)
      fun t₂ ⟨⟨h12, hdx, hcx, hm₂⟩, k₂⟩ => ?_)
    have hc₂ := hc₁.mem hm₂ k₂ (by decide)
    refine WP.mono (setWord_ok hc₂.good.scr hc₂.good.rdi hc₂.good.hdr hZ h12 (by omega) hw' (o := aY) (by decide)
      (ri := .rcx) (by decide) (i := 0) (by omega) hcx) fun t' ⟨hv, ho, k₃⟩ => ?_
    have ha : Arrays B w [aY] t₂.mem t'.mem := Arrays.of_outside (j := aY) (by simp) ho (Nat.le_refl _) (Nat.le_refl _)
    refine ⟨⟨hc₂.good.scr.congr k₃.2.2, (k₃.gpr (by decide)).trans hc₂.good.rdi, ha.hdr hc₂.good.hdr⟩, ?_, ?_,
      ((k₁.trans k₂).trans k₃).mono (by decide)⟩
    · rw [hv, hdx, h0]
      simp only [Nat.pow_zero, Nat.mul_zero, Nat.mod_eq_of_lt hN1]; rfl
    · rw [hm₂, hm₁] at ha
      exact Frm.of_arrays ha (by simp [finRanges])
  · refine WP.ite true (by simp [eval, hz₁, h0]) (fun _ => ?_) (by simp)
    refine WP.mono (mm_ok (o := aY) (a := aY) (b := aOne) hc₁.good hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hc₁.inv
      (by rw [hc₁.n, hm₁, hone]; exact hN1)) fun t' ⟨hg', hlt, hmm, ha, k₂⟩ => ?_
    rw [hc₁.n] at hlt
    rw [hc₁.n, hm₁, hY, hone, Nat.mul_one] at hmm
    refine ⟨hg', ?_, by rw [hm₁] at ha; exact Frm.of_arrays ha (by simp [finRanges]), (k₁.trans k₂).mono (by decide)⟩
    rw [← Nat.mod_eq_of_lt hlt]
    exact VG.Proof.Bignum.mont_cancel hR (by rw [hmm, hYc])

end VG.Proof.Bignum.X86_64
