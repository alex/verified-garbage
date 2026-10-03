import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Spec.Rsa
import Mathlib.Tactic.Positivity

/-!
# Multiword arithmetic on x86-64: bytes and words

`loadBE` reads `k` bytes, most significant first, into the `⌈k / 8⌉` words of
an array: as a number, OS2IP of the bytes (`loadBE_ok`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem sx7 : BitVec.signExtend 64 (7 : BitVec 32) = 7 := by decide

theorem and7_eq (p : Nat) (hp : p < 2 ^ 64) : (BitVec.ofNat 64 p &&& 7 == 0) = decide (p % 8 = 0) := by
  have h : (BitVec.ofNat 64 p &&& 7).toNat = p % 8 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
      show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  by_cases h0 : p % 8 = 0
  · simp only [h0, decide_true, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq; rw [h, h0]; rfl
  · simp only [h0, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h0; rw [← h, he]; rfl

theorem shr3_eq (p : Nat) (hp : p < 2 ^ 64) : BitVec.ofNat 64 p >>> 3 = BitVec.ofNat 64 (p / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem test_eq (x : BitVec 64) : (x &&& x == 0) = (x == 0) := by rw [BitVec.and_self]

theorem ror56_toNat (x : BitVec 64) (h : x.toNat < 2 ^ 56) : (x.rotateRight 56).toNat = x.toNat * 256 := by
  rw [BitVec.toNat_rotateRight, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.div_eq_of_lt (by simpa using h), Nat.zero_or]
  simp only [show 56 % 64 = 56 from rfl, show 64 - 56 = 8 from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- `loadByte`: `p := p - 1`, `rax := 256 rax + byte`, `r14 += 1`, ZF iff
`8 ∣ p - 1`. -/
theorem loadByte_ok {t : State} {p : Nat} {a : Addr} {b : Byte} (hp1 : 1 ≤ p) (hp : p < 2 ^ 63)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 p) (hax : (t.gpr .rax).toNat < 2 ^ 56) (h14 : t.gpr .r14 = a)
    (ha : InRegions (t.rd ++ t.wr) a 1) (hb : t.mem a = b) :
    WP isa (.block loadByte) t fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (p - 1) ∧ (t'.gpr .rax).toNat = (t.gpr .rax).toNat * 256 + b.toNat ∧
      t'.gpr .r14 = a + 1 ∧ t'.zf = some (decide ((p - 1) % 8 = 0)) ∧ t'.mem = t.mem ∧
      Keep [.rax, .rdx, .rbp, .r14] t t' := by
  have hpred : BitVec.ofNat 64 p - 1 = BitVec.ofNat 64 (p - 1) := ofNat64_pred hp1 (by omega)
  refine WP.mono (WP.keep [.rax, .rdx, .rbp, .r14] (c := .block loadByte) (Q := fun t' =>
      t'.gpr .rdx = BitVec.ofNat 64 (p - 1) ∧ (t'.gpr .rax).toNat = (t.gpr .rax).toNat * 256 + b.toNat ∧
      t'.gpr .r14 = a + 1 ∧ t'.zf = some (decide ((p - 1) % 8 = 0)) ∧ t'.mem = t.mem) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, k⟩
  unfold loadByte
  xrun [State.ea, at0, hdx, h14, hpred, ha, hb, sx7, and7_eq (p - 1) (by omega),
    show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]
  rw [BitVec.toNat_add, ror56_toNat _ hax, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (b := 2 ^ 64)
    (by have := b.isLt; omega), Nat.mod_eq_of_lt (by have := b.isLt; omega)]

/-- `storeWord`: `rax` as word `p / 8` of the array at `rbx = B + ed`. -/
theorem storeWord_ok {t : State} {B : Addr} {Z ed p : Nat} (hs : Scr t B Z) (hp : p < 2 ^ 63)
    (hdx : t.gpr .rdx = BitVec.ofNat 64 p) (hbx : t.gpr .rbx = off B ed) (hed : ed + 8 * (p / 8) + 8 ≤ Z) :
    WP isa (.block storeWord) t fun t' =>
      t'.mem = t.mem.writeW (off B (ed + 8 * (p / 8))) (t.gpr .rax) ∧ t'.gpr .rax = 0 ∧
      Keep [.rax, .rbp] t t' := by
  refine WP.mono (WP.keep [.rax, .rbp] (c := .block storeWord) (Q := fun t' =>
      t'.mem = t.mem.writeW (off B (ed + 8 * (p / 8))) (t.gpr .rax) ∧ t'.gpr .rax = 0) ?_ rfl)
    fun t' ⟨h, k⟩ => ⟨h.1, h.2, k⟩
  unfold storeWord
  xrun [State.ea, ix, hdx, shr3_eq p (by omega), addr0 hbx rfl, hs.st hed]

/-! ## The loop of `loadBE` -/

/-- OS2IP of the first `i` bytes. -/
def pre (bs : List Byte) (i : Nat) : Nat := Spec.Rsa.os2ip (bs.take i)

theorem pre_succ (bs : List Byte) {i : Nat} (hi : i < bs.length) :
    pre bs (i + 1) = 256 * pre bs i + (bs[i]).toNat := by
  unfold pre Spec.Rsa.os2ip
  rw [← List.take_concat_get hi, List.concat_eq_append, List.foldl_append]
  rfl

theorem pre_zero (bs : List Byte) : pre bs 0 = 0 := rfl

theorem pre_len (bs : List Byte) : pre bs bs.length = Spec.Rsa.os2ip bs := by
  unfold pre; rw [List.take_length]

theorem pow256 (a : Nat) : (256 : Nat) ^ (8 * a) = 2 ^ (64 * a) := by
  rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]; congr 1; omega

/-- Words that are the base-`2⁶⁴` digits of `V` make `V mod 2^(64 n)`. -/
theorem wv_digits {m : Mem} {B : Addr} {ed V : Nat} (n : Nat)
    (h : ∀ q < n, word m B (ed + 8 * q) = BitVec.ofNat 64 (V / 256 ^ (8 * q))) :
    wv m B ed n = V % 2 ^ (64 * n) := by
  induction n with
  | zero => simp [wv, Nat.mod_one]
  | succ n ih =>
    rw [wv, ih fun q hq => h q (by omega), h n (by omega), BitVec.toNat_ofNat, pow256,
      show 64 * (n + 1) = 64 * n + 64 by omega, Nat.pow_add, Nat.mod_mul]

/-- After `i` bytes of `loadBE` from `s₀`, with `p = k - i` bytes left. -/
structure LInv (s₀ : State) (B : Addr) (Z ed k w : Nat) (src : Addr) (bs : List Byte) (i : Nat)
    (t : State) : Prop where
  scr : Scr t B Z
  keep : Keep [.rax, .rdx, .rbp, .r14] s₀ t
  rdx : t.gpr .rdx = BitVec.ofNat 64 (k - i)
  r14 : t.gpr .r14 = src + BitVec.ofNat 64 i
  rax : (t.gpr .rax).toNat = pre bs i % 256 ^ ((8 - (k - i) % 8) % 8)
  words : ∀ q < w, k - i ≤ 8 * q → word t.mem B (ed + 8 * q) = BitVec.ofNat 64 (pre bs i / 256 ^ (8 * q - (k - i)))
  out : Outside B ed (8 * w) s₀.mem t.mem

theorem loadStep_ok {s₀ : State} {B : Addr} {Z ed k w : Nat} {src : Addr} {bs : List Byte}
    (hk : bs.length = k) (hk' : k < 2 ^ 31) (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hbx : s₀.gpr .rbx = off B ed)
    (hsrc : ∀ i < k, InRegions (s₀.rd ++ s₀.wr) (src + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < k), s₀.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i))
    {i : Nat} (hi : i < k) {t : State} (hI : LInv s₀ B Z ed k w src bs i t) :
    WP isa (.seq (.block loadByte) (.seq (.ite .e (.block storeWord) (.block []))
      (.block [.alu .test .rdx (.reg .rdx)]))) t fun t' =>
      t'.zf = some (decide (i + 1 = k)) ∧ LInv s₀ B Z ed k w src bs (i + 1) t' := by
  have hn := hI.scr.nowrap
  have tbx : t.gpr .rbx = off B ed := (hI.keep.gpr (by decide)).trans hbx
  have hr7 : (8 - (k - i) % 8) % 8 ≤ 7 := by omega
  have hax : (t.gpr .rax).toNat < 2 ^ 56 := by
    rw [hI.rax]
    have : 256 ^ ((8 - (k - i) % 8) % 8) ≤ 256 ^ 7 := Nat.pow_le_pow_right (by norm_num) hr7
    have := Nat.mod_lt (pre bs i) (show 0 < 256 ^ ((8 - (k - i) % 8) % 8) by positivity)
    have : (256 : Nat) ^ 7 = 2 ^ 56 := by norm_num
    omega
  have hb : t.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega) := by
    rw [hI.out _ (hsep i hi)]; exact hbytes i hi
  have hld : InRegions (t.rd ++ t.wr) (src + BitVec.ofNat 64 i) 1 := by
    rw [hI.keep.2.1, hI.keep.2.2]; exact hsrc i hi
  refine WP.seq (WP.mono (loadByte_ok (p := k - i) (by omega) (by omega) hI.rdx hax hI.r14 hld hb)
    fun t₁ ⟨hdx₁, hax₁, h14₁, hz₁, hm₁, k₁⟩ => ?_)
  have hpre := pre_succ bs (i := i) (by omega)
  -- The new partial word.
  have hax₁' : (t₁.gpr .rax).toNat = pre bs (i + 1) % 256 ^ ((8 - (k - i) % 8) % 8 + 1) := by
    rw [hax₁, hI.rax, hpre, VG.Proof.Bignum.bytes_mod_step _ _ _ (bs[i]'(by omega)).isLt]
    ring
  have hs₁ := hI.scr.congr k₁.2.2
  have tbx₁ : t₁.gpr .rbx = off B ed := (k₁.gpr (by decide)).trans tbx
  -- The old words, one byte on.
  have hwords : ∀ q < w, k - i ≤ 8 * q → word t.mem B (ed + 8 * q) =
      BitVec.ofNat 64 (pre bs (i + 1) / 256 ^ (8 * q - (k - (i + 1)))) := by
    intro q hq hle
    rw [hI.words q hq hle, hpre, show 8 * q - (k - (i + 1)) = 8 * q - (k - i) + 1 by omega,
      VG.Proof.Bignum.bytes_div_step _ _ _ (bs[i]'(by omega)).isLt]
  by_cases hz : (k - i - 1) % 8 = 0
  · -- A word is complete: it is stored.
    refine WP.seq (WP.ite true (by simp [eval, hz₁, hz]) (fun _ => ?_) (by simp))
    refine WP.mono (storeWord_ok hs₁ (p := k - i - 1) (by omega) hdx₁ tbx₁ (by omega))
      fun t₂ ⟨hm₂, hax₂, k₂⟩ => ?_
    refine WP.mono (WP.keep [.rdx] (c := .block [.alu .test .rdx (.reg .rdx)])
      (Q := fun t' => t'.zf = some (decide (i + 1 = k)) ∧ t'.mem = t₂.mem ∧
        t'.gpr .rdx = BitVec.ofNat 64 (k - i - 1)) (by
        xrun [(k₂.gpr (by decide) : t₂.gpr .rdx = t₁.gpr .rdx), hdx₁, test_eq,
          ofNat64_beq_zero (show k - i - 1 < 2 ^ 64 by omega)]
        exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩) rfl)
      fun t' ⟨⟨hz', hm', hdx'⟩, k'⟩ => ⟨hz', ?_⟩
    refine ⟨hs₁.congr (k'.2.2.trans k₂.2.2), ((hI.keep.trans k₁).trans (k₂.trans k')).mono (by decide),
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdx']; congr 1
    · rw [(k'.gpr (by decide) : t'.gpr .r14 = t₂.gpr .r14), (k₂.gpr (by decide) : t₂.gpr .r14 = t₁.gpr .r14),
        h14₁, BitVec.add_assoc, ofNat_add_one]
    · rw [(k'.gpr (by decide) : t'.gpr .rax = t₂.gpr .rax), hax₂,
        show (8 - (k - (i + 1)) % 8) % 8 = 0 by omega, Nat.pow_zero, Nat.mod_one]; rfl
    · intro q hq hle
      rw [hm', hm₂, hm₁]
      by_cases hq' : 8 * q = k - i - 1
      · have : q = (k - i - 1) / 8 := by omega
        subst this
        rw [word_writeW_self, show 8 * ((k - i - 1) / 8) - (k - (i + 1)) = 0 by omega, Nat.pow_zero,
          Nat.div_one]
        apply BitVec.eq_of_toNat_eq
        rw [hax₁', BitVec.toNat_ofNat, show (8 - (k - i) % 8) % 8 + 1 = 8 by omega,
          VG.Proof.Bignum.pow256_8]
      · rw [(writeW_outside t.mem B _ (by omega)).word (by omega) (by omega)]
        exact hwords q hq (by omega)
    · rw [hm', hm₂, hm₁]
      intro x hx
      rw [writeW_outside t.mem B _ (by omega) x (by omega)]
      exact hI.out x hx
  · -- No word is complete.
    refine WP.seq (WP.ite false (by simp [eval, hz₁, hz]) (by simp) (fun _ => WP.block_nil ?_))
    refine WP.mono (WP.keep [.rdx] (c := .block [.alu .test .rdx (.reg .rdx)])
      (Q := fun t' => t'.zf = some (decide (i + 1 = k)) ∧ t'.mem = t₁.mem ∧
        t'.gpr .rdx = BitVec.ofNat 64 (k - i - 1)) (by
        xrun [hdx₁, test_eq, ofNat64_beq_zero (show k - i - 1 < 2 ^ 64 by omega)]
        exact decide_eq_decide.mpr ⟨fun _ => by omega, fun _ => by omega⟩) rfl)
      fun t' ⟨⟨hz', hm', hdx'⟩, k'⟩ => ⟨hz', ?_⟩
    refine ⟨hs₁.congr k'.2.2, ((hI.keep.trans k₁).trans k').mono (by decide), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hdx']; congr 1
    · rw [(k'.gpr (by decide) : t'.gpr .r14 = t₁.gpr .r14), h14₁, BitVec.add_assoc, ofNat_add_one]
    · rw [(k'.gpr (by decide) : t'.gpr .rax = t₁.gpr .rax), hax₁',
        show (8 - (k - i) % 8) % 8 + 1 = (8 - (k - (i + 1)) % 8) % 8 by omega]
    · intro q hq hle
      rw [hm', hm₁]
      exact hwords q hq (by omega)
    · rw [hm', hm₁]; exact hI.out

theorem pre_lt (bs : List Byte) {i : Nat} (hi : i ≤ bs.length) : pre bs i < 256 ^ i := by
  induction i with
  | zero => exact Nat.one_pos
  | succ i ih =>
    rw [pre_succ bs (by omega), Nat.pow_succ]
    have := ih (by omega)
    have := (bs[i]'(by omega)).isLt
    omega

/-- `loadBE`: the `k` bytes at `rsi`, most significant first, as the
`w = ⌈k / 8⌉` words of the array at `rbx`. -/
theorem loadBE_ok {s : State} {B : Addr} {Z ed k w : Nat} {src : Addr} {bs : List Byte}
    (hs : Scr s B Z) (hsi : s.gpr .rsi = src) (hcx : s.gpr .rcx = BitVec.ofNat 64 k)
    (hbx : s.gpr .rbx = off B ed) (hk : bs.length = k) (hk1 : 1 ≤ k) (hk' : k < 2 ^ 31)
    (hw : w = (k + 7) / 8) (hed : ed + 8 * w ≤ Z)
    (hsrc : ∀ i < k, InRegions (s.rd ++ s.wr) (src + BitVec.ofNat 64 i) 1)
    (hbytes : ∀ i (h : i < k), s.mem (src + BitVec.ofNat 64 i) = bs[i]'(by omega))
    (hsep : ∀ i < k, ofs B (src + BitVec.ofNat 64 i) < ed ∨ ed + 8 * w ≤ ofs B (src + BitVec.ofNat 64 i)) :
    WP isa loadBE s fun t =>
      wv t.mem B ed w = Spec.Rsa.os2ip bs ∧ Outside B ed (8 * w) s.mem t.mem ∧
      Keep [.rax, .rdx, .rbp, .r14] s t := by
  unfold loadBE
  refine WP.seq (WP.mono (WP.keep [.rax, .rdx, .r14] (Q := fun t => t.gpr .rax = 0 ∧
      t.gpr .rdx = BitVec.ofNat 64 k ∧ t.gpr .r14 = src ∧ t.mem = s.mem) (by xrun [hcx, hsi]) rfl)
    fun s₁ ⟨⟨hax, hdx, h14, hm₁⟩, k₁⟩ => ?_)
  have hs₁ := hs.congr k₁.2.2
  refine wp_upto (a := 0) (N := k) (by omega) (LInv s B Z ed k w src bs) ?_
    (fun t hI => ⟨?_, hI.out, hI.keep⟩) ⟨hs₁, k₁.mono (by decide), by rw [hdx, Nat.sub_zero], by
      rw [h14]; exact (BitVec.add_zero src).symm, by rw [hax, pre_zero]; rfl,
      fun q hq hle => absurd hle (by omega), by rw [hm₁]; exact Outside.refl _ _ _ _⟩
  · intro i _ hi t hI
    exact loadStep_ok hk hk' hw hed hbx hsrc hbytes hsep hi hI
  · rw [wv_digits w fun q hq => by rw [hI.words q hq (by omega), Nat.sub_self, Nat.sub_zero],
      ← hk, pre_len, Nat.mod_eq_of_lt]
    have := pre_lt bs (Nat.le_refl _)
    rw [pre_len, hk] at this
    have : (256 : Nat) ^ k ≤ 2 ^ (64 * w) := by
      rw [← pow256]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end VG.Proof.Bignum.X86_64
