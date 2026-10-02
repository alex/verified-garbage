import VerifiedGarbage.Proof.MlKem.Bits

/-!
# ML-DSA: streaming `d`-bit fields through an accumulator, for every target

An implementation packs a group of fields, the base-`2ᵈ` digits of a number
`G`, by adding each field to an accumulator above the bits it holds, and
storing each byte it completes; it unpacks the fields of `H`, the number whose
bytes are the group's, by adding each byte it needs to an accumulator, and
taking the low `d` bits. The accumulator is always a slice of the number:

* packing, before field `j`: `G mod 2^(dj)` without its `⌊dj/8⌋` bytes
  already stored, `G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8))`, which is less
  than `2^(dj mod 8)` (`pack_acc_lt`); adding field `j` (`pack_add`) and
  shifting out bytes (`pack_shift`, each the byte of `G` at its position,
  `pack_byte`) keeps it so;
* unpacking, before field `j`: the bytes loaded, `⌈dj/8⌉` (`Impl`'s `need`),
  without the `d · j` bits taken, `H % 2 ^ (8 * t) / 2 ^ (d * j)` for
  `t` bytes, less than `2^(8t - dj)` (`unpack_acc_lt`); adding byte `t`
  (`unpack_add`) keeps it so, and once `d(j + 1) ≤ 8t` its low `d` bits are
  field `j` (`unpack_field`) and the rest the accumulator of field `j + 1`
  (`unpack_shift`).
-/

namespace VG.Proof.MlDsa.Pack

open VG.Proof.MlKem (digits digits_chunk digits_cons digits_nil digits_lt mod_pow_div_mod take_drop_eq)

/-- Digit `j` of the number whose base-`2ᵈ` digits are `V 0, …, V (c - 1)`. -/
theorem digits_range_get {d c j : Nat} {V : Nat → Nat} (hV : ∀ j < c, V j < 2 ^ d) (hj : j < c) :
    digits d ((List.range c).map V) / 2 ^ (d * j) % 2 ^ d = V j := by
  have hL : ∀ a ∈ (List.range c).map V, a < 2 ^ d := fun a ha => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha; exact hV u (List.mem_range.mp hu)
  have h := digits_chunk hL j 1
  rw [Nat.mul_one] at h
  rw [h, take_drop_eq _ 0 (by rw [List.length_map, List.length_range]; omega)]
  simp only [List.range_one, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.mul_zero, Nat.add_zero,
    Nat.add_zero, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]

theorem digits_range_lt {d c : Nat} {V : Nat → Nat} (hV : ∀ j < c, V j < 2 ^ d) :
    digits d ((List.range c).map V) < 2 ^ (d * c) := by
  have := digits_lt (w := d) (L := (List.range c).map V) fun a ha => by
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha; exact hV u (List.mem_range.mp hu)
  rwa [List.length_map, List.length_range] at this

theorem two_pow_split {a b : Nat} (h : b ≤ a) : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- `X mod 2^(a + b) = X mod 2^a + 2^a · (⌊X / 2^a⌋ mod 2^b)`. -/
theorem mod_two_pow_add (X a b : Nat) : X % 2 ^ (a + b) = X % 2 ^ a + 2 ^ a * (X / 2 ^ a % 2 ^ b) := by
  rw [Nat.pow_add, Nat.mod_mul]

/-- `(X mod 2^a) / 2^b < 2^(a - b)`. -/
theorem mod_div_lt (X a b : Nat) : X % 2 ^ a / 2 ^ b < 2 ^ (a - b) := by
  rcases Nat.le_total b a with h | h
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos b), ← Nat.pow_add, show a - b + b = a by omega]
    exact Nat.mod_lt _ (Nat.two_pow_pos a)
  · rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos a))
      (Nat.pow_le_pow_right (by decide) h))]
    exact Nat.two_pow_pos _

/-! ## Packing -/

theorem pack_acc_lt (G d j : Nat) : G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) < 2 ^ (d * j % 8) := by
  have := mod_div_lt G (d * j) (8 * (d * j / 8))
  rwa [show d * j - 8 * (d * j / 8) = d * j % 8 by omega] at this

/-- Adding field `j`, `⌊G / 2^(dj)⌋ mod 2ᵈ`, above the `dj mod 8` bits of
the accumulator. -/
theorem pack_add (G d j : Nat) :
    G % 2 ^ (d * j) / 2 ^ (8 * (d * j / 8)) + G / 2 ^ (d * j) % 2 ^ d * 2 ^ (d * j % 8) =
      G % 2 ^ (d * (j + 1)) / 2 ^ (8 * (d * j / 8)) := by
  rw [Nat.mul_succ, mod_two_pow_add, two_pow_split (show 8 * (d * j / 8) ≤ d * j by omega),
    show d * j - 8 * (d * j / 8) = d * j % 8 by omega, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_comm (2 ^ (d * j % 8))]

/-- The low byte of the accumulator after `u` bytes shifted out of the one
of `k` bytes stored: byte `k + u` of `G`, if the first `a` bits are in. -/
theorem pack_byte (G a k u : Nat) (h : 8 * (k + u) + 8 ≤ a) :
    G % 2 ^ a / 2 ^ (8 * k) / 2 ^ (8 * u) % 2 ^ 8 = G / 2 ^ (8 * (k + u)) % 2 ^ 8 := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.mul_add, mod_pow_div_mod _ h]

theorem pack_shift (G a k u : Nat) :
    G % 2 ^ a / 2 ^ (8 * k) / 2 ^ (8 * u) = G % 2 ^ a / 2 ^ (8 * (k + u)) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, ← Nat.mul_add]

/-! ## Unpacking -/

theorem unpack_acc_lt (H t e : Nat) : H % 2 ^ (8 * t) / 2 ^ e < 2 ^ (8 * t - e) := mod_div_lt H _ _

/-- Adding byte `t`, `⌊H / 2^(8t)⌋ mod 2⁸`, above the `8t - e` bits of the
accumulator. -/
theorem unpack_add (H t e : Nat) (h : e ≤ 8 * t) :
    H % 2 ^ (8 * t) / 2 ^ e + H / 2 ^ (8 * t) % 2 ^ 8 * 2 ^ (8 * t - e) = H % 2 ^ (8 * (t + 1)) / 2 ^ e := by
  rw [Nat.mul_succ, mod_two_pow_add, two_pow_split h, Nat.mul_assoc,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.mul_comm (2 ^ (8 * t - e))]

/-- The low `d` bits of the accumulator, once it holds them: field `j`. -/
theorem unpack_field (H t d j : Nat) (h : d * (j + 1) ≤ 8 * t) :
    H % 2 ^ (8 * t) / 2 ^ (d * j) % 2 ^ d = H / 2 ^ (d * j) % 2 ^ d :=
  mod_pow_div_mod _ (by rw [Nat.mul_succ] at h; exact h)

theorem unpack_shift (H t d j : Nat) : H % 2 ^ (8 * t) / 2 ^ (d * j) / 2 ^ d = H % 2 ^ (8 * t) / 2 ^ (d * (j + 1)) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ]

end VG.Proof.MlDsa.Pack
