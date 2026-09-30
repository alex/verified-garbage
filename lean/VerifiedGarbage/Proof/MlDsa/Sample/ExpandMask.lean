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

/-- The bits of a prefix are those of the whole. -/
theorem leNat_take_bits (L : List Byte) {k P c : Nat} (h : P + c ≤ 8 * k) :
    leNat (L.take k) / 2 ^ P % 2 ^ c = leNat L / 2 ^ P % 2 ^ c := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_div_two_pow,
    testBit_leNat, testBit_leNat]
  by_cases hj : j < c
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by omega)]
  · simp [hj]

/-- The width `c = 1 + bitlen (γ₁ - 1)` of the coefficients of `ExpandMask`. -/
def emC (γ : Nat) : Nat := if γ = 2 ^ 17 then 18 else 20

theorem emC_eq {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) :
    1 + bitlen (γ - 1) = emC γ ∧ bitlen (γ - 1 + γ) = emC γ ∧ γ = 2 ^ (emC γ - 1) := by
  rcases hγ with rfl | rfl <;> decide

/-- Coefficient `i` of the polynomial of `ExpandMask`, from the first 640
bytes `X` of the output (at least the `32c` it unpacks). -/
theorem expandMask_getElem (ρ : List Byte) {γ : Nat} (hγ : γ = 2 ^ 17 ∨ γ = 2 ^ 19) {i : Nat} (hi : i < 256) :
    (toRq (bitUnpack (H ρ (32 * (1 + bitlen (γ - 1)))) (γ - 1) γ))[i]! =
      ofInt ((γ : Int) - (leNat (H ρ 640) / 2 ^ (i * emC γ) % 2 ^ emC γ : Nat)) := by
  obtain ⟨e1, e2, _⟩ := emC_eq hγ
  have hc : emC γ ≤ 20 := by unfold emC; split <;> omega
  rw [getElem!_pos _ i hi]
  simp only [toRq, Vector.getElem_map]
  rw [bitUnpack_getElem _ _ _ hi, e1, e2,
    ← H_take ρ (show 32 * emC γ ≤ 640 by omega), leNat_take_bits _ (by
      have : i * emC γ + emC γ ≤ 256 * emC γ := by
        have := Nat.mul_le_mul_right (emC γ) (show i + 1 ≤ 256 by omega); rw [Nat.add_mul] at this; omega
      omega)]

/-! ## The sign bits of `SampleInBall` -/

/-- Bit `k` of the sign bits: bit `k` of the first 8 bytes of the output, as
a little-endian integer. -/
theorem signs_getD (X : List Byte) (k : Nat) :
    (signs X).getD k false = (leNat (X.take 8)).testBit k := by
  rw [signs, bytesToBits_getD_testBit]

theorem bStep_ge {τ : Nat} {h : Array Bool} (st : IPoly × Nat) (j : Byte) : st.2 ≤ (bStep τ h st j).2 := by
  unfold bStep; split
  · split <;> simp
  · exact Nat.le_refl _

theorem bFold_ge {τ : Nat} {h : Array Bool} : ∀ (st : IPoly × Nat) (L : List Byte), st.2 ≤ (bFold τ h st L).2
  | st, j :: L => by rw [bFold]; exact Nat.le_trans (bStep_ge st j) (bFold_ge _ L)
  | _, [] => Nat.le_refl _

/-- Coefficient `k` after setting coefficient `i`. -/
theorem ipoly_set!_get (c : IPoly) {k : Nat} (i : Nat) (hk : k < n) (x : Int) :
    (c.set! i x)[k]! = if i = k then x else c[k]! := by
  rw [getElem!_pos _ k hk, getElem!_pos _ k hk, Vector.getElem_set!]

end VG.Proof.MlDsa.Sample
