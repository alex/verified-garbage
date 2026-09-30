import VerifiedGarbage.Proof.MlDsa.Sample.Ball

/-!
# ML-DSA: `BitUnpack` as arithmetic on the bytes

Untrusted: everything here is checked by Lean. The bits of a byte string
`v` (`bytesToBits`) are those of the integer `leNat v` whose little-endian
encoding it is (`bytesToBits_getD_testBit`); so the `c` bits of
coefficient `i` of `BitUnpack` are `⌊leNat v / 2^(ic)⌋ mod 2^c`
(`bitUnpack_getElem`), which an implementation computes from the few bytes
that hold them.
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa

/-- The integer whose little-endian encoding is `v`. -/
def leNat : List Byte → Nat
  | [] => 0
  | c :: v => c.toNat + 2 ^ 8 * leNat v

/-- Bit `k` of `leNat v`: bit `k mod 8` of byte `⌊k/8⌋` (0 past the end). -/
theorem testBit_leNat : ∀ (v : List Byte) (k : Nat), (leNat v).testBit k = (v.getD (k / 8) 0).getLsbD (k % 8)
  | [], k => by simp [leNat]
  | c :: v, k => by
    rw [leNat, Nat.add_comm, Nat.testBit_two_pow_mul_add _ c.isLt]
    split
    · rename_i h
      rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      rfl
    · rename_i h
      rw [testBit_leNat v, show k / 8 = (k - 8) / 8 + 1 by omega, List.getD_cons_succ,
        show k % 8 = (k - 8) % 8 by omega]

theorem bytesToBits_size (v : List Byte) : (bytesToBits v).size = 8 * v.length := by
  simp only [bytesToBits, List.size_toArray]
  induction v with
  | nil => rfl
  | cons c v ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_range, ih, List.length_cons]
    omega

/-- Bit `k` of the bits of `v`. -/
theorem bytesToBits_getD_testBit (v : List Byte) (k : Nat) :
    (bytesToBits v).getD k false = (leNat v).testBit k := by
  rw [testBit_leNat]
  by_cases hk : k < 8 * v.length
  · exact bytesToBits_getD v hk
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [bytesToBits_size]; omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

/-- The integer of `c` bits of `X` from bit `P`. -/
theorem bitsToInteger_testBit (X : Nat) : ∀ (c P : Nat),
    bitsToInteger ((List.range c).map fun j => X.testBit (P + j)) = X / 2 ^ P % 2 ^ c
  | 0, P => by simp [bitsToInteger, Nat.mod_one]
  | c + 1, P => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have ih := bitsToInteger_testBit X c (P + 1)
    have e : ((fun j => X.testBit (P + j)) ∘ Nat.succ) = fun j => X.testBit (P + 1 + j) := by
      funext j; simp only [Function.comp]; congr 1; omega
    simp only [bitsToInteger, List.foldr_cons] at ih ⊢
    rw [e, ih, Nat.add_zero]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [show 2 * (X / 2 ^ (P + 1) % 2 ^ c) = 2 ^ 1 * (X / 2 ^ (P + 1) % 2 ^ c) by rfl,
      Nat.testBit_two_pow_mul_add _ (by cases X.testBit P <;> decide), Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
    split
    · rename_i h
      have : i = 0 := by omega
      subst this
      have := testBit_eq X P
      cases hb : X.testBit P <;> rw [hb] at this <;> simp at this <;> simp <;> omega
    · rename_i h
      rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, show i - 1 + (P + 1) = i + P by omega]
      congr 1
      exact decide_eq_decide.mpr (by omega)

/-- Coefficient `i` of `BitUnpack(v, a, b)`: `b` minus the `c` bits of
`leNat v` from bit `ic`, for `c = bitlen (a + b)`. -/
theorem bitUnpack_getElem (v : List Byte) (a b : Nat) {i : Nat} (hi : i < n) :
    (bitUnpack v a b)[i] = (b : Int) - (leNat v / 2 ^ (i * bitlen (a + b)) % 2 ^ bitlen (a + b) : Nat) := by
  simp only [bitUnpack, Vector.getElem_ofFn, bytesToBits_getD_testBit]
  rw [bitsToInteger_testBit]

end VG.Proof.MlDsa.Sample
