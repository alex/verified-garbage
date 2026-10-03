import VerifiedGarbage.Proof.Bignum.X86_64.R2
import VerifiedGarbage.Proof.Bignum.X86_64.Mont

/-!
# Multiword arithmetic on x86-64: the exponentiation of `vg_rsa_public`

`Good t B Z w minv`: the working space, its base in `rdi`, and the header.
`mm_ok` is `montMul_ok` for `vg_rsa_public`'s arrays. `expBit` squares `Y`
and multiplies it by `X` if the bit is set (`expBit_ok`); `expLoop` does it
for every bit of `e`, most significant first (`expLoop_ok`): `Y ≡ x^e R`.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem bit7 (V : Nat) (hV : V < 2 ^ 64) :
    ((BitVec.ofNat 64 V >>> 7) &&& 1 == 0) = decide (V / 128 % 2 = 0) := by
  have h : ((BitVec.ofNat 64 V >>> 7) &&& 1).toNat = V / 128 % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV,
      Nat.shiftRight_eq_div_pow, show (1 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  by_cases h0 : V / 128 % 2 = 0
  · simp only [h0, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, h0]; rfl
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; rw [← h, he]; rfl

/-- What a bit of the exponentiation changes: arrays and header slots. -/
def bitRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w aAcc, 8 * (w + 2)), (slot w aTmp, 8 * (w + 2)), (slot w aY, 8 * (w + 2)), (8 * sV, 8),
    (8 * sBit, 8)]

/-- What the exponentiation changes: also the byte index. -/
def expRanges (w : Nat) : List (Nat × Nat) := (8 * sI, 8) :: bitRanges w

/-- An array that `Arrays` does not list keeps its value. -/
theorem Arrays.wv_of_not_mem {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {j : Nat} (hj : j < 8) (hn : j ∉ js) (hZ : B.toNat + slot w 8 ≤ 2 ^ 64) :
    wv m' B (slot w j) w = wv m B (slot w j) w :=
  h.wv_eq (fun k hk => by
    have := slot_sep (w := w) (show j ≠ k from fun e => hn (e ▸ hk)); omega)
    (by have := slot_le (w := w) hj; omega)

theorem Arrays.word0_of_not_mem {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    {j : Nat} (hj : j < 8) (hn : j ∉ js) (hZ : B.toNat + slot w 8 ≤ 2 ^ 64) (hw : 1 ≤ w) :
    word m' B (slot w j) = word m B (slot w j) :=
  h.word_eq (fun k hk => by
    have := slot_sep (w := w) (show j ≠ k from fun e => hn (e ▸ hk)); omega)
    (by have := slot_le (w := w) hj; omega)

theorem Arrays.hslot {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {i : Nat}
    (hi : i < 32) : word m' B (8 * i) = word m B (8 * i) :=
  h.word_eq (fun j _ => Or.inl (hdr_lt_slot w j hi)) (by omega)

theorem bit_step {v tb : Nat} (htb : tb < 8) :
    2 * (v / 2 ^ (8 - tb)) + v * 2 ^ tb / 128 % 2 = v / 2 ^ (7 - tb) := by
  have h1 : v * 2 ^ tb / 128 = v / 2 ^ (7 - tb) := by
    rw [show (128 : Nat) = 2 ^ tb * 2 ^ (7 - tb) by rw [← Nat.pow_add, show tb + (7 - tb) = 7 by omega],
      Nat.mul_comm v, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
  rw [h1, show 8 - tb = (7 - tb) + 1 by omega, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  omega

/-- What the exponentiation keeps: the working space, the modulus `N` (and
its low word, for `-m⁻¹`), and `X ≡ x R`. -/
structure ExpCtx (t : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X : Nat) : Prop where
  good : Good t B Z w minv
  n : wv t.mem B (slot w aN) w = N
  inv : ((word t.mem B (slot w aN)).toNat * minv.toNat + 1) % 2 ^ 64 = 0
  x : wv t.mem B (slot w aXm) w = X

theorem ExpCtx.of_arrays {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hg : Good t' B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w)
    (ha : Arrays B w [aAcc, aTmp, aY] t.mem t'.mem) : ExpCtx t' B Z w minv N X := by
  have hn : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
  exact ⟨hg, by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hc.n,
    by rw [ha.word0_of_not_mem (by decide) (by decide) hn hw]; exact hc.inv,
    by rw [ha.wv_of_not_mem (by decide) (by decide) hn]; exact hc.x⟩

/-- One bit of `e`: `Y ≡ x^E R` becomes `x^(2E + bit) R`, for the bit at the
top of the byte `V / 128 mod 2`; `V` doubles and the bit count `b` drops. -/
theorem expBit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E Y V b : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hY : wv t.mem B (slot w aY) w = Y) (hYN : Y < N) (hYc : Y % N = x ^ E * 2 ^ (64 * w) % N)
    (hV : word t.mem B (8 * sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 62)
    (hb : word t.mem B (8 * sBit) = BitVec.ofNat 64 b) (hb1 : 1 ≤ b) (hb' : b < 2 ^ 31) :
    WP isa expBit t fun t' => ExpCtx t' B Z w minv N X ∧
      (∃ Y', wv t'.mem B (slot w aY) w = Y' ∧ Y' < N ∧ Y' % N = x ^ (2 * E + V / 128 % 2) * 2 ^ (64 * w) % N) ∧
      word t'.mem B (8 * sV) = BitVec.ofNat 64 (V + V) ∧ word t'.mem B (8 * sBit) = BitVec.ofNat 64 (b - 1) ∧
      t'.zf = some (decide (b - 1 = 0)) ∧ Frm B (bitRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have eV : sV = 25 := rfl
  have eB : sBit = 24 := rfl
  have h8 : 256 ≤ slot w 0 := by unfold slot hdrBytes; omega
  unfold expBit
  -- `Y := Y²`.
  refine WP.seq (WP.mono (Mont.base.mm_ok (o := aY) (a := aY) (b := aY) hc.good hZ hw hw' (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hc.inv (by rw [hY, hc.n]; exact hYN))
    fun t₁ ⟨hg₁, hlt₁, hm₁, ha₁, k₁⟩ => ?_)
  rw [hc.n] at hlt₁
  rw [hc.n, hY] at hm₁
  have hc₁ := hc.of_arrays hg₁ hZ (by omega) ha₁
  have hY₁ : wv t₁.mem B (slot w aY) w % N = x ^ (2 * E) * 2 ^ (64 * w) % N :=
    VG.Proof.Bignum.mont_sq hR hYc hm₁
  have hV₁ : word t₁.mem B (8 * sV) = BitVec.ofNat 64 V := by rw [ha₁.hslot (by decide)]; exact hV
  have hb₁ : word t₁.mem B (8 * sBit) = BitVec.ofNat 64 b := by rw [ha₁.hslot (by decide)]; exact hb
  have hl : ∀ i < 32, InRegions (t₁.rd ++ t₁.wr) (off B (8 * i)) 8 := fun i hi =>
    hg₁.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  -- The bit, into ZF.
  refine WP.seq (WP.mono (WP.keep [.rax] (Q := fun t₂ => t₂.zf = some (decide (V / 128 % 2 = 0)) ∧
      t₂.mem = t₁.mem) (by
    unfold bitTest
    xrun [State.ea, hdr, hg₁.rdi, hdrOff, hl sV (by decide), hV₁, bit7 V (by omega)]) rfl)
    fun t₂ ⟨⟨hz₂, hm₂⟩, k₂⟩ => ?_)
  have hg₂ : Good t₂ B Z w minv := ⟨hg₁.scr.congr k₂.2.2, (k₂.gpr (by decide)).trans hg₁.rdi, hm₂ ▸ hg₁.hdr⟩
  have hc₂ : ExpCtx t₂ B Z w minv N X := ⟨hg₂, hm₂ ▸ hc₁.n, hm₂ ▸ hc₁.inv, hm₂ ▸ hc₁.x⟩
  -- `Y := Y X` if the bit is set; the rest as on entry to it.
  have hmul : WP isa (.ite .ne (mm aY aY aXm) (.block [])) t₂ fun t₃ => ExpCtx t₃ B Z w minv N X ∧
      wv t₃.mem B (slot w aY) w < N ∧
      wv t₃.mem B (slot w aY) w % N = x ^ (2 * E + V / 128 % 2) * 2 ^ (64 * w) % N ∧
      Arrays B w [aAcc, aTmp, aY] t₂.mem t₃.mem ∧ Keep mmRegs t₂ t₃ := by
    by_cases hbit : V / 128 % 2 = 0
    · refine WP.ite false (by simp [eval, hz₂, hbit]) (by simp) (fun _ => WP.block_nil ⟨hc₂, ?_, ?_,
        fun _ _ => rfl, Keep.refl _ _⟩)
      · rw [hm₂]; exact hlt₁
      · rw [hm₂, hY₁, hbit, Nat.add_zero]
    · refine WP.ite true (by simp [eval, hz₂, hbit]) (fun _ => ?_) (by simp)
      refine WP.mono (Mont.base.mm_ok (o := aY) (a := aY) (b := aXm) hg₂ hZ hw hw' (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hc₂.inv
        (by rw [hc₂.x, hc₂.n]; exact hXN)) fun t₃ ⟨hg₃, hlt₃, hm₃, ha₃, k₃⟩ => ?_
      rw [hc₂.n] at hlt₃
      rw [hc₂.n, hc₂.x] at hm₃
      refine ⟨hc₂.of_arrays hg₃ hZ (by omega) ha₃, hlt₃, ?_, ha₃, k₃⟩
      rw [show V / 128 % 2 = 1 by omega]
      have hY₂ : wv t₂.mem B (slot w aY) w % N = x ^ (2 * E) * 2 ^ (64 * w) % N := by rw [hm₂]; exact hY₁
      exact VG.Proof.Bignum.mont_mulx hR hY₂ hXc hm₃
  refine WP.seq (WP.mono hmul fun t₃ ⟨hc₃, hlt₃, hY₃, ha₃, k₃⟩ => ?_)
  -- The next bit.
  have hV₃ : word t₃.mem B (8 * sV) = BitVec.ofNat 64 V := by rw [ha₃.hslot (by decide), hm₂]; exact hV₁
  have hb₃ : word t₃.mem B (8 * sBit) = BitVec.ofNat 64 b := by rw [ha₃.hslot (by decide), hm₂]; exact hb₁
  have hl₃ : ∀ i < 32, InRegions (t₃.rd ++ t₃.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₃.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₃ : ∀ i < 32, InRegions t₃.wr (off B (8 * i)) 8 := fun i hi =>
    hc₃.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hV₃' : (t₃.mem.writeW (off B (8 * sV)) (BitVec.ofNat 64 (V + V))).readW (off B (8 * sBit)) 64 =
      BitVec.ofNat 64 b := by
    rw [← hb₃]; exact (writeW_outside _ B _ (by omega)).word (by unfold sV sBit sFn; omega) (by omega)
  refine WP.mono (WP.keep [.rax] (Q := fun t' => t'.mem = (t₃.mem.writeW (off B (8 * sV))
      (BitVec.ofNat 64 (V + V))).writeW (off B (8 * sBit)) (BitVec.ofNat 64 (b - 1)) ∧
      t'.zf = some (decide (b - 1 = 0))) (by
    unfold bitNext
    xrun [State.ea, hdr, hc₃.good.rdi, hdrOff, hl₃ sV (by decide), hs₃ sV (by decide), hV₃, hV₃',
      hs₃ sBit (by decide), hl₃ sBit (by decide), ← BitVec.ofNat_add,
      ofNat64_pred hb1 (by omega), ofNat64_beq_zero (show b - 1 < 2 ^ 64 by omega)]) rfl)
    fun t' ⟨⟨hm', hz'⟩, k'⟩ => ?_
  have o1 := writeW_outside t₃.mem B (BitVec.ofNat 64 (V + V)) (d := 8 * sV) (by unfold sV sFn; omega)
  have o2 := writeW_outside (t₃.mem.writeW (off B (8 * sV)) (BitVec.ofNat 64 (V + V))) B
    (BitVec.ofNat 64 (b - 1)) (d := 8 * sBit) (by omega)
  have hfr : Frm B (bitRanges w) t.mem t'.mem := by
    rw [hm']
    exact (((Frm.of_arrays ha₁ (by simp [bitRanges])).trans (by rw [hm₂]; exact Frm.refl _ _ _)).trans
      (Frm.of_arrays ha₃ (by simp [bitRanges]))).trans
      ((Frm.of_outside o1 (by simp [bitRanges])).trans (Frm.of_outside o2 (by simp [bitRanges])))
  have hgood : Good t' B Z w minv := ⟨hc₃.good.scr.congr k'.2.2, (k'.gpr (by decide)).trans hc₃.good.rdi,
    by rw [hm']; exact Hdr.store (Hdr.store hc₃.good.hdr (by decide) (by decide) _) (by decide) (by decide) _⟩
  have hY' : wv t'.mem B (slot w aY) w = wv t₃.mem B (slot w aY) w := by
    rw [hm', o2.wv (by unfold sBit sFn; have := hdr_lt_slot w aY (show sBit < 32 by decide); omega)
      (by have := slot_le (w := w) (show aY < 8 by decide); omega),
      o1.wv (by have := hdr_lt_slot w aY (show sV < 32 by decide); omega)
      (by have := slot_le (w := w) (show aY < 8 by decide); omega)]
  refine ⟨?_, ⟨_, hY', hlt₃, hY₃⟩, ?_, ?_, hz', hfr,
    (((k₁.trans k₂).trans k₃).trans k').mono (by decide)⟩
  · -- The header stores are below the arrays: the modulus and `X` are as before.
    have hkeep : ∀ j < 8, j ≠ aY → j ≠ aAcc → j ≠ aTmp →
        wv t'.mem B (slot w j) w = wv t₃.mem B (slot w j) w := fun j hj _ _ _ => by
      rw [hm', o2.wv (by have := hdr_lt_slot w j (show sBit < 32 by decide); omega)
        (by have := slot_le (w := w) hj; omega),
        o1.wv (by have := hdr_lt_slot w j (show sV < 32 by decide); omega)
        (by have := slot_le (w := w) hj; omega)]
    have hw0 : word t'.mem B (slot w aN) = word t₃.mem B (slot w aN) := by
      have := slot_le (w := w) (show aN < 8 by decide)
      rw [hm', o2.word (by have := hdr_lt_slot w aN (show sBit < 32 by decide); omega) (by omega),
        o1.word (by have := hdr_lt_slot w aN (show sV < 32 by decide); omega) (by omega)]
    exact ⟨hgood, by rw [hkeep aN (by decide) (by decide) (by decide) (by decide)]; exact hc₃.n,
      by rw [hw0]; exact hc₃.inv, by rw [hkeep aXm (by decide) (by decide) (by decide) (by decide)]; exact hc₃.x⟩
  · rw [hm', o2.word (by unfold sV sBit sFn; omega) (by omega), word_writeW_self]
  · rw [hm', word_writeW_self]

/-- After `j` bits of the byte `v` from `t₀`, where `Y ≡ x^E R`. -/
structure BitInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x E v : Nat) (j : Nat)
    (t : State) : Prop where
  ctx : ExpCtx t B Z w minv N X
  y : ∃ Y, wv t.mem B (slot w aY) w = Y ∧ Y < N ∧ Y % N = x ^ (E * 2 ^ j + v / 2 ^ (8 - j)) * 2 ^ (64 * w) % N
  v : word t.mem B (8 * sV) = BitVec.ofNat 64 (v * 2 ^ j)
  b : word t.mem B (8 * sBit) = BitVec.ofNat 64 (8 - j)
  frm : Frm B (bitRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

/-- Bit `j` of the byte `v`. -/
theorem bitStep_ok {t s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) {j : Nat} (hj : j < 8) (hI : BitInv t B Z w minv N X x E v j s) :
    WP isa expBit s fun s' => s'.zf = some (decide (j + 1 = 8)) ∧ BitInv t B Z w minv N X x E v (j + 1) s' := by
  obtain ⟨Y, hY, hYN, hYc⟩ := hI.y
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine WP.mono (expBit_ok hI.ctx hZ hw hw' hR hXN hXc hY hYN hYc hI.v
    (by have := Nat.mul_le_mul_left v hp; omega) hI.b (by omega) (by omega))
    fun s' ⟨hc', ⟨Y', hY', hYN', hYc'⟩, hV', hb', hz', hfr', k'⟩ => ⟨?_, ⟨hc', ⟨Y', hY', hYN', ?_⟩, ?_, ?_,
      hI.frm.trans hfr', (hI.keep.trans k').mono (by simp [mmRegs])⟩⟩
  · rw [hz']; congr 1; exact decide_eq_decide.mpr (by omega)
  · rw [hYc', show 2 * (E * 2 ^ j + v / 2 ^ (8 - j)) + v * 2 ^ j / 128 % 2 =
      E * 2 ^ (j + 1) + v / 2 ^ (8 - (j + 1)) by
        rw [Nat.mul_add, Nat.add_assoc, bit_step (by omega), show 7 - j = 8 - (j + 1) by omega,
          Nat.pow_succ, Nat.mul_comm 2 (E * 2 ^ j), Nat.mul_assoc]]
  · rw [hV', ← Nat.two_mul, Nat.pow_succ]; congr 1; rw [Nat.mul_comm, Nat.mul_assoc]
  · rw [hb']; congr 1

/-- The eight bits of the byte `v`: `Y ≡ x^E R` becomes `x^(256 E + v) R`. -/
theorem bits_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x E v : Nat}
    (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hv : v < 256) (h0 : BitInv t B Z w minv N X x E v 0 t) :
    WP isa (.loop expBit .ne) t (BitInv t B Z w minv N X x E v 8) :=
  wp_upto (a := 0) (N := 8) (by decide) (BitInv t B Z w minv N X x E v)
    (fun _ _ hj _ hI => bitStep_ok hZ hw hw' hR hXN hXc hv hj hI) (fun _ h => h) h0

/-- A store to a header slot keeps the arrays. -/
theorem hdrStore_wv (m : Mem) (B : Addr) {w i j : Nat} (v : BitVec 64) (hi : i < 32) (hj : j < 8)
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    wv (m.writeW (off B (8 * i)) v) B (slot w j) w = wv m B (slot w j) w :=
  (writeW_outside m B v (by omega)).wv (by have := hdr_lt_slot w j hi; omega)
    (by have := slot_le (w := w) hj; omega)

theorem hdrStore_word (m : Mem) (B : Addr) {w i j : Nat} (v : BitVec 64) (hi : i < 32) (hj : j < 8)
    (hn : B.toNat + slot w 8 ≤ 2 ^ 64) :
    word (m.writeW (off B (8 * i)) v) B (slot w j) = word m B (slot w j) :=
  (writeW_outside m B v (by omega)).word (by have := hdr_lt_slot w j hi; omega)
    (by have := slot_le (w := w) hj; omega)

/-- Another header slot. -/
theorem hdrStore_hdr (m : Mem) (B : Addr) {i k : Nat} (v : BitVec 64) (hi : i < 32) (hk : k < 32)
    (hik : i ≠ k) : word (m.writeW (off B (8 * i)) v) B (8 * k) = word m B (8 * k) :=
  (writeW_outside m B v (by omega)).word (by omega) (by omega)

/-- `ExpCtx` after a store to a slot of the functions' own. -/
theorem ExpCtx.store {t t' : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X : Nat}
    (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) {i : Nat} (hi : 16 ≤ i) (hi' : i < 32)
    {v : BitVec 64} (hm : t'.mem = t.mem.writeW (off B (8 * i)) v) (hwr : t'.wr = t.wr)
    (hdi : t'.gpr .rdi = B) : ExpCtx t' B Z w minv N X := by
  have hn : B.toNat + slot w 8 ≤ 2 ^ 64 := by have := hc.good.scr.nowrap; omega
  exact ⟨⟨hc.good.scr.congr hwr, hdi, hm ▸ Hdr.store hc.good.hdr hi hi' v⟩,
    by rw [hm, hdrStore_wv _ _ _ hi' (by decide) hn]; exact hc.n,
    by rw [hm, hdrStore_word _ _ _ hi' (by decide) hn]; exact hc.inv,
    by rw [hm, hdrStore_wv _ _ _ hi' (by decide) hn]; exact hc.x⟩

/-- After `i` bytes of `e` (`L` bytes `eb` at `ep`) from `t₀`. -/
structure ByteInv (t₀ : State) (B : Addr) (Z w : Nat) (minv : BitVec 64) (N X x : Nat) (ep : Addr)
    (L : Nat) (eb : List Byte) (i : Nat) (t : State) : Prop where
  ctx : ExpCtx t B Z w minv N X
  y : ∃ Y, wv t.mem B (slot w aY) w = Y ∧ Y < N ∧ Y % N = x ^ pre eb i * 2 ^ (64 * w) % N
  idx : word t.mem B (8 * sI) = BitVec.ofNat 64 i
  e : word t.mem B (8 * sE) = ep
  len : word t.mem B (8 * sElen) = BitVec.ofNat 64 L
  frm : Frm B (expRanges w) t₀.mem t.mem
  keep : Keep mmRegs t₀ t

theorem expRanges_le (w : Nat) : ∀ r ∈ expRanges w, r.1 + r.2 ≤ slot w 8 := by
  have h := hdr_lt_slot w 0 (i := sBit) (by decide)
  have h1 := slot_le (w := w) (show aAcc < 8 by decide)
  have h2 := slot_le (w := w) (show aTmp < 8 by decide)
  have h3 := slot_le (w := w) (show aY < 8 by decide)
  have h4 : slot w 0 ≤ slot w aAcc := by unfold slot; omega
  simp only [expRanges, bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp only [sI, sV, sBit, sFn] at * <;> omega

theorem bitRanges_sub (w : Nat) : ∀ r ∈ bitRanges w, r ∈ expRanges w :=
  fun _ hr => List.mem_cons_of_mem _ hr

/-- A header slot that a bit of the exponentiation does not change. -/
theorem bitRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h1 : k ≠ sV) (h2 : k ≠ sBit) :
    ∀ r ∈ bitRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  have h := hdr_lt_slot w aAcc hk
  have h' := hdr_lt_slot w aTmp hk
  have h'' := hdr_lt_slot w aY hk
  simp only [bitRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl) <;> simp only [sV, sBit, sFn] at * <;> omega

theorem expRanges_hdr (w : Nat) {k : Nat} (hk : k < 32) (h0 : k ≠ sI) (h1 : k ≠ sV) (h2 : k ≠ sBit) :
    ∀ r ∈ expRanges w, 8 * k + 8 ≤ r.1 ∨ r.1 + r.2 ≤ 8 * k := by
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · simp only [sI, sFn] at *; omega
  · exact bitRanges_hdr w hk h1 h2 r hr

theorem byteRead (ep : Addr) (i : Nat) :
    ep + BitVec.ofNat 64 i * BitVec.ofNat 64 1 + BitVec.ofInt 64 0 = ep + BitVec.ofNat 64 i := by
  rw [show BitVec.ofNat 64 1 = 1#64 from rfl, BitVec.mul_one, show BitVec.ofInt 64 0 = 0#64 from rfl,
    BitVec.add_zero]

theorem setWidth_byte (b : Byte) : b.setWidth 64 = BitVec.ofNat 64 (b.toNat * 2 ^ 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.pow_zero, Nat.mul_one,
    Nat.mod_eq_of_lt (by have := b.isLt; omega)]

theorem sw8 : BitVec.setWidth 64 (8 : BitVec 32) = BitVec.ofNat 64 (8 - 0) := rfl

theorem byteHead_eq : byteHead = ([.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI))] : List Instr) ++
    ([.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr sV) .rax, .mov32 .rax (.imm 8),
      .store (hdr sBit) .rax] : List Instr) := rfl

/-- `byteHead`'s loads: `e` and the byte index. -/
theorem byteHead1_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hI : ByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI))]) t fun t₁ =>
      t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧ ByteInv t₀ B Z w minv N X x ep L eb i t₁ := by
  have hc := hI.ctx
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  refine WP.mono (WP.keep [.rax, .rcx] (Q := fun t₁ => t₁.gpr .rax = ep ∧ t₁.gpr .rcx = BitVec.ofNat 64 i ∧
      t₁.mem = t.mem) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sE (by decide), hl sI (by decide), hI.e, hI.idx]) rfl)
    fun t₁ ⟨⟨h1, h2, hm⟩, k⟩ => ⟨h1, h2, ?_⟩
  exact ⟨⟨⟨hc.good.scr.congr k.2.2, (k.gpr (by decide)).trans hc.good.rdi, hm ▸ hc.good.hdr⟩, hm ▸ hc.n,
    hm ▸ hc.inv, hm ▸ hc.x⟩, hm ▸ hI.y, hm ▸ hI.idx, hm ▸ hI.e, hm ▸ hI.len, hm ▸ hI.frm,
    (hI.keep.trans k).mono (by decide)⟩

/-- `byteHead`'s byte of `e` into `sV`, and the bit count 8: the start of the
bits. -/
theorem byteHead2_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hL : eb.length = L) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i))
    (hI : ByteInv t₀ B Z w minv N X x ep L eb i t) (hax : t.gpr .rax = ep)
    (hcx : t.gpr .rcx = BitVec.ofNat 64 i) :
    WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr sV) .rax,
      .mov32 .rax (.imm 8), .store (hdr sBit) .rax]) t fun t₁ =>
      t₁.mem = (t.mem.writeW (off B (8 * sV)) ((eb[i]'(by omega)).setWidth 64)).writeW (off B (8 * sBit))
        (BitVec.setWidth 64 (8 : BitVec 32)) ∧ Keep [.rax] t t₁ ∧
      BitInv t₁ B Z w minv N X x (pre eb i) (eb[i]'(by omega)).toNat 0 t₁ := by
  have hc := hI.ctx
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  have hs : ∀ i < 32, InRegions t.wr (off B (8 * i)) 8 := fun i hi =>
    hc.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hrdi : InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hrd i hi
  have hbi : t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega) := by
    rw [hI.frm _ fun r hr => Or.inr (by have := expRanges_le w r hr; have := hout i hi; omega)]
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
  obtain ⟨Y, hY, hYN, hYc⟩ := hI.y
  refine ⟨hc₁, ⟨Y, ?_, hYN, ?_⟩, ?_, ?_, Frm.refl _ _ _, Keep.refl _ _⟩
  · rw [hm₁, hdrStore_wv (i := sBit) (j := aY) _ _ _ (by decide) (by decide) hn',
      hdrStore_wv (i := sV) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hY
  · rw [hYc, Nat.pow_zero, Nat.mul_one, Nat.sub_zero, Nat.div_eq_of_lt (show _ < 2 ^ 8 from hv), Nat.add_zero]
  · rw [hm₁, hdrStore_hdr (i := sBit) (k := sV) _ _ _ (by decide) (by decide) (by decide),
      word_writeW_self, setWidth_byte]
  · rw [hm₁, word_writeW_self]; rfl

/-- One byte of `e`: its eight bits, then the next byte. -/
theorem byte_ok {t₀ t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x : Nat} {ep : Addr} {L : Nat}
    {eb : List Byte} {i : Nat} (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N) (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hL : eb.length = L) (hL' : L < 2 ^ 31) (hi : i < L)
    (hrd : ∀ i < L, InRegions (t₀.rd ++ t₀.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t₀.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i))
    (hI : ByteInv t₀ B Z w minv N X x ep L eb i t) :
    WP isa (.seq (.block byteHead) (.seq (.loop expBit .ne) (.block byteNext))) t fun t' =>
      t'.zf = some (decide (i + 1 = L)) ∧ ByteInv t₀ B Z w minv N X x ep L eb (i + 1) t' := by
  have hn := hI.ctx.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  rw [byteHead_eq]
  refine WP.seq ((WP.block_append_iff).mpr (WP.mono (byteHead1_ok hZ hI) fun tₐ ⟨hax, hcx, hIₐ⟩ =>
    WP.mono (byteHead2_ok hZ hL hi hrd hbytes hout hIₐ hax hcx) fun t₁ ⟨hm₁, k₁, hB0⟩ => ?_))
  have hv : (eb[i]'(by omega)).toNat < 256 := (eb[i]'(by omega)).isLt
  refine WP.seq (WP.mono (bits_ok hZ hw hw' hR hXN hXc hv hB0) fun t₂ h₂ => ?_)
  -- The next byte.
  have hc₂ := h₂.ctx
  have hl₂ : ∀ i < 32, InRegions (t₂.rd ++ t₂.wr) (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.ld (by have := hdr_lt_slot w 8 hi; omega)
  have hs₂ : ∀ i < 32, InRegions t₂.wr (off B (8 * i)) 8 := fun i hi =>
    hc₂.good.scr.st (by have := hdr_lt_slot w 8 hi; omega)
  have hh₂ : ∀ k < 32, k ≠ sV → k ≠ sBit → word t₂.mem B (8 * k) = word tₐ.mem B (8 * k) := fun k hk h1 h2 => by
    rw [h₂.frm.word_eq (bitRanges_hdr w hk h1 h2) (by omega), hm₁,
      hdrStore_hdr (i := sBit) _ _ _ (by decide) hk (Ne.symm h2),
      hdrStore_hdr (i := sV) _ _ _ (by decide) hk (Ne.symm h1)]
  have hidx₂ := (hh₂ sI (by decide) (by decide) (by decide)).trans hIₐ.idx
  have he₂ := (hh₂ sE (by decide) (by decide) (by decide)).trans hIₐ.e
  have hlen₂ := (hh₂ sElen (by decide) (by decide) (by decide)).trans hIₐ.len
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
  obtain ⟨Y₂, hY₂, hYN₂, hYc₂⟩ := h₂.y
  refine ⟨ExpCtx.store hc₂ hZ (i := sI) (by decide) (by decide) hm' k'.2.2 ((k'.gpr (by decide)).trans
    hc₂.good.rdi), ⟨Y₂, ?_, hYN₂, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm', hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hY₂
  · rw [hYc₂, pre_succ eb (by omega), Nat.pow_zero, Nat.div_one, Nat.mul_comm (pre eb i)]; rfl
  · rw [hm', word_writeW_self]
  · rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact he₂
  · rw [hm', hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen₂
  · have f₁ : Frm B (expRanges w) tₐ.mem t₁.mem := by
      rw [hm₁]
      exact (Frm.of_outside (writeW_outside tₐ.mem B _ (d := 8 * sV) (by unfold sV sFn; omega)) (by simp [expRanges, bitRanges])).trans
        (Frm.of_outside (writeW_outside _ B _ (d := 8 * sBit) (by unfold sBit sFn; omega)) (by simp [expRanges, bitRanges]))
    have f₃ : Frm B (expRanges w) t₂.mem t'.mem := by
      rw [hm']; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * sI) (by unfold sI sFn; omega)) (by simp [expRanges])
    exact ((hIₐ.frm.trans f₁).trans (h₂.frm.mono (bitRanges_sub w))).trans f₃
  · exact (((hIₐ.keep.trans k₁).trans h₂.keep).trans k').mono (by decide)

/-- `expLoop`'s start: byte index 0. -/
theorem expInit_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x Y : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z)
    (hY : wv t.mem B (slot w aY) w = Y) (hYN : Y < N) (hYc : Y % N = 2 ^ (64 * w) % N)
    (he : word t.mem B (8 * sE) = ep) (hlen : word t.mem B (8 * sElen) = BitVec.ofNat 64 L) :
    WP isa (.block [.mov32 .rax (.imm 0), .store (hdr sI) .rax]) t
      (ByteInv t B Z w minv N X x ep L eb 0) := by
  have hn := hc.good.scr.nowrap
  have hn' : B.toNat + slot w 8 ≤ 2 ^ 64 := by omega
  refine WP.mono (WP.keep [.rax] (Q := fun t₁ => t₁.mem = t.mem.writeW (off B (8 * sI))
      (BitVec.setWidth 64 (0 : BitVec 32))) (by
    xrun [State.ea, hdr, hc.good.rdi, hdrOff,
      hc.good.scr.st (d := 8 * sI) (by have := hdr_lt_slot w 8 (show sI < 32 by decide); omega)]) rfl)
    fun t₁ ⟨hm₁, k₁⟩ => ?_
  refine ⟨ExpCtx.store hc hZ (i := sI) (by decide) (by decide) hm₁ k₁.2.2
      ((k₁.gpr (by decide)).trans hc.good.rdi), ⟨Y, ?_, hYN, ?_⟩, ?_, ?_, ?_, ?_, k₁.mono (by decide)⟩
  · rw [hm₁, hdrStore_wv (i := sI) (j := aY) _ _ _ (by decide) (by decide) hn']; exact hY
  · rw [hYc, pre_zero, Nat.pow_zero, Nat.one_mul]
  · rw [hm₁, word_writeW_self]; rfl
  · rw [hm₁, hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact he
  · rw [hm₁, hdrStore_hdr (i := sI) _ _ _ (by decide) (by decide) (by decide)]; exact hlen
  · rw [hm₁]; exact Frm.of_outside (writeW_outside _ B _ (d := 8 * sI) (by unfold sI sFn; omega))
      (by simp [expRanges])

/-- The exponentiation: `Y ≡ R` becomes `Y ≡ x^e R`, for the `L` bytes `eb`
of `e` at `ep`, outside the working space. -/
theorem expLoop_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} {N X x Y : Nat} {ep : Addr}
    {L : Nat} {eb : List Byte} (hc : ExpCtx t B Z w minv N X) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w)
    (hw' : w < 2 ^ 31) (hR : Nat.Coprime (2 ^ (64 * w)) N) (hXN : X < N)
    (hXc : X % N = x * 2 ^ (64 * w) % N)
    (hY : wv t.mem B (slot w aY) w = Y) (hYN : Y < N) (hYc : Y % N = 2 ^ (64 * w) % N)
    (he : word t.mem B (8 * sE) = ep) (hlen : word t.mem B (8 * sElen) = BitVec.ofNat 64 L)
    (hL : eb.length = L) (hL1 : 1 ≤ L) (hL' : L < 2 ^ 31)
    (hrd : ∀ i < L, InRegions (t.rd ++ t.wr) (ep + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < L), t.mem (ep + BitVec.ofNat 64 i) = eb[i]'(by omega))
    (hout : ∀ i < L, Z ≤ ofs B (ep + BitVec.ofNat 64 i)) :
    WP isa expLoop t fun t' => ExpCtx t' B Z w minv N X ∧
      (∃ Y', wv t'.mem B (slot w aY) w = Y' ∧ Y' < N ∧
        Y' % N = x ^ Spec.Rsa.os2ip eb * 2 ^ (64 * w) % N) ∧
      Frm B (expRanges w) t.mem t'.mem ∧ Keep mmRegs t t' := by
  unfold expLoop
  refine WP.seq (WP.mono (expInit_ok (x := x) (eb := eb) hc hZ hY hYN hYc he hlen) fun t₁ h₁ => ?_)
  refine wp_upto (a := 0) (N := L) (by omega) (ByteInv t B Z w minv N X x ep L eb)
    (fun i _ hi s hI => byte_ok hZ hw hw' hR hXN hXc hL hL' hi hrd hbytes hout hI)
    (fun s hI => ?_) h₁
  obtain ⟨Y', h1, h2, h3⟩ := hI.y
  exact ⟨hI.ctx, ⟨Y', h1, h2, by rw [h3, ← hL, pre_len]⟩, hI.frm, hI.keep⟩

end VG.Proof.Bignum.X86_64
