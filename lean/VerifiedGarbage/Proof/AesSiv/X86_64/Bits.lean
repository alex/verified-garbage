import VerifiedGarbage.Proof.Siv.Spec
import VerifiedGarbage.Proof.Cmac.Mem
import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
import VerifiedGarbage.Proof.Gcm.X86_64.Bits

/-!
# AES-SIV on x86-64: words and bits

* The counter `Q + i` is stored as a 128-bit block (big-endian, as
  `Spec.Gcm.toBytes`), which is the RFC's `be128` of the number
  (`toBytes_be128`); the code increments it a 64-bit word at a time, with
  `add` and `adc` on the byte-reversed halves (`inc_words`).
* The counter `Q`: the IV's second word ANDed with `0xffffff7fffffff7f`
  clears bit 7 of its bytes 8 and 12 (`counter_words`).
* The comparison of the IVs: `(¬a ∧ (a − 1)) >> 63` is 1 exactly if `a` is 0
  (`eqz`), and `a`, the OR of the XORs of the halves, is 0 exactly if the IVs
  are equal (`or_xor_eq_zero`).
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64 Proof.Cmac
open VG.Proof.CmacAes.X86_64 (getD_le8_append)

/-! ## The counter as a block -/

theorem toBytes_be128 (x : Nat) : Spec.Gcm.toBytes (BitVec.ofNat 128 x) = Spec.Siv.be128 x := by
  simp only [Spec.Gcm.toBytes, Spec.Siv.be128]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have : 2 ^ 128 = 2 ^ (8 * (15 - i)) * 2 ^ (128 - 8 * (15 - i)) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega)),
    show 256 ^ (15 - i) = 2 ^ (8 * (15 - i)) by rw [Nat.pow_mul]]

theorem beNat_eq (q : List Byte) : Spec.Gcm.ofBytes q = BitVec.ofNat 128 (Spec.Siv.beNat q) := rfl

/-- The counter block of CTR for block `i`: `be128 (beNat q + i)` is the
block of `q` plus `i`, as bytes. -/
theorem be128_add (q : List Byte) (i : Nat) :
    Spec.Siv.be128 (Spec.Siv.beNat q + i) = Spec.Gcm.toBytes (Spec.Gcm.ofBytes q + BitVec.ofNat 128 i) := by
  rw [← toBytes_be128, beNat_eq, BitVec.ofNat_add]

/-- `add 1` on the low word and `adc 0` on the high word increment the
128-bit integer `hi ++ lo`. -/
theorem inc_words (hi lo : BitVec 64) :
    ((hi + BitVec.signExtend 64 (0 : BitVec 32) +
        (BitVec.ofBool (decide (2 ^ 64 ≤ lo.toNat + (BitVec.signExtend 64 (1 : BitVec 32)).toNat))).setWidth 64 :
          BitVec 64) ++ (lo + BitVec.signExtend 64 (1 : BitVec 32) : BitVec 64) : BitVec 128) =
      (hi ++ lo : BitVec 128) + (1 : BitVec 128) := by
  have h0 : BitVec.signExtend 64 (0 : BitVec 32) = 0 := by decide
  have h1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  rw [h0, h1]
  apply BitVec.eq_of_toNat_eq
  have hl := lo.isLt
  have hh := hi.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
    show (1 : BitVec 64).toNat = 1 from rfl, show (1 : BitVec 128).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)),
    ← Nat.shiftLeft_add_eq_or_of_lt hl, Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  by_cases h : 2 ^ 64 ≤ lo.toNat + 1
  · have : lo.toNat = 2 ^ 64 - 1 := by omega
    rw [decide_eq_true h, Bool.toNat_true, this]
    omega
  · rw [decide_eq_false h, Bool.toNat_false]
    omega

/-! ## The counter `Q` -/

/-- The mask of the IV's second word: bit 7 of its bytes 0 and 4 (the IV's
bytes 8 and 12) cleared. -/
def qmask : BitVec 64 := 0xffffff7fffffff7f

theorem extractLsb'_and (a b : BitVec 64) (k : Nat) :
    (a &&& b).extractLsb' (8 * k) 8 = a.extractLsb' (8 * k) 8 &&& b.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  simp [hj]

theorem qmask_byte : ∀ k < 8, qmask.extractLsb' (8 * k) 8 = if k = 0 ∨ k = 4 then 0x7f else 0xff := by
  decide

/-- The two words of the IV, the second ANDed with `qmask`, are the bytes of
the counter `Q`. -/
theorem counter_words (w₀ w₁ : BitVec 64) :
    le8 w₀ ++ le8 (w₁ &&& qmask) = Spec.Siv.counter (le8 w₀ ++ le8 w₁) := by
  refine ext16 (by simp [length_le8]) (by simp [Spec.Siv.counter]) fun k hk => ?_
  simp only [Spec.Siv.counter, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some]
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge k 8 with h8 | h8
  · rw [getD_le8_append _ _ hk, getD_le8_append _ _ hk]
    simp only [h8, ↓reduceIte]
    split
    · omega
    · rfl
  · rw [getD_le8_append _ _ hk, getD_le8_append _ _ hk]
    simp only [show ¬ k < 8 by omega, ↓reduceIte]
    rw [extractLsb'_and, qmask_byte (k - 8) (by omega)]
    by_cases hk' : k = 8 ∨ k = 12
    · simp only [show (k - 8 = 0 ∨ k - 8 = 4) = True from eq_true (by omega), hk', ite_true]
    · simp only [show (k - 8 = 0 ∨ k - 8 = 4) = False from eq_false (by omega), hk', ite_false]
      apply BitVec.eq_of_getLsbD_eq; intro j hj
      simp only [BitVec.getLsbD_and]
      have : (0xff : Byte).getLsbD j = true := by revert j; decide
      rw [this, Bool.and_true]

/-! ## Comparing the IVs -/

/-- `(¬a ∧ (a − 1)) >> 63`: 1 if `a` is 0, else 0. -/
theorem eqz (a : BitVec 64) :
    ((a ^^^ BitVec.signExtend 64 (0xffffffff : BitVec 32)) &&& (a - BitVec.signExtend 64 (1 : BitVec 32))) >>> 63 =
      if a = 0 then 1 else 0 := by
  have e1 : BitVec.signExtend 64 (0xffffffff : BitVec 32) = BitVec.allOnes 64 := by decide
  have e2 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  rw [e1, e2, BitVec.xor_allOnes]
  split
  · subst_vars; decide
  · rename_i h
    have h0 : a.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and, BitVec.toNat_not,
      BitVec.toNat_sub, show (1 : BitVec 64).toNat = 1 from rfl, show (0 : BitVec 64).toNat = 0 from rfl]
    have ha := a.isLt
    apply Nat.div_eq_of_lt
    by_cases hm : a.toNat < 2 ^ 63
    · calc _ ≤ (2 ^ 64 - 1 + a.toNat) % 2 ^ 64 := Nat.and_le_right
        _ < 2 ^ 63 := by rw [show 2 ^ 64 - 1 + a.toNat = (a.toNat - 1) + 2 ^ 64 by omega, Nat.add_mod_right,
            Nat.mod_eq_of_lt (by omega)]; omega
    · calc _ ≤ 2 ^ 64 - 1 - a.toNat := Nat.and_le_left
        _ < 2 ^ 63 := by omega

theorem le8_inj {a b : BitVec 64} (h : le8 a = le8 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  have := congrArg (fun l => (l.getD (j / 8) 0).getLsbD (j % 8)) h
  simp only [getD_le8 _ (show j / 8 < 8 by omega), BitVec.getLsbD_extractLsb',
    show j % 8 < 8 by omega, decide_true, Bool.true_and] at this
  rwa [show 8 * (j / 8) + j % 8 = j by omega] at this

theorem or_xor_eq_zero (v₀ t₀ v₁ t₁ : BitVec 64) :
    ((v₀ ^^^ t₀) ||| (v₁ ^^^ t₁)) = 0 ↔ v₀ = t₀ ∧ v₁ = t₁ := by
  constructor
  · intro h
    have hb : ∀ j < 64, v₀.getLsbD j = t₀.getLsbD j ∧ v₁.getLsbD j = t₁.getLsbD j := by
      intro j _
      have := congrArg (fun x : BitVec 64 => x.getLsbD j) h
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor] at this
      have z : (0 : BitVec 64).getLsbD j = false := by simp
      rw [z] at this
      revert this
      cases v₀.getLsbD j <;> cases t₀.getLsbD j <;> cases v₁.getLsbD j <;> cases t₁.getLsbD j <;> simp
    exact ⟨BitVec.eq_of_getLsbD_eq fun j hj => (hb j hj).1, BitVec.eq_of_getLsbD_eq fun j hj => (hb j hj).2⟩
  · rintro ⟨rfl, rfl⟩; simp

/-- Two 16-byte blocks, as two words each, are equal exactly if their words are. -/
theorem le8_append_eq (v₀ t₀ v₁ t₁ : BitVec 64) :
    le8 v₀ ++ le8 v₁ = le8 t₀ ++ le8 t₁ ↔ v₀ = t₀ ∧ v₁ = t₁ := by
  constructor
  · intro h
    have := List.append_inj h (by simp [length_le8])
    exact ⟨le8_inj this.1, le8_inj this.2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- A byte ANDed with the mask `0 − r` of a result `r` of 0 or 1. -/
theorem mask_byte (b : Byte) (c : Bool) :
    ((b.setWidth 64 &&& ((0 : BitVec 64) - (if c then 1 else 0))).setWidth 8) = if c then b else 0 := by
  cases c
  · simp
  · rw [show (if true = true then (1 : BitVec 64) else 0) = 1 from rfl,
      show (0 : BitVec 64) - 1 = BitVec.allOnes 64 by decide, BitVec.and_allOnes]
    simp

end VG.Proof.AesSiv.X86_64
