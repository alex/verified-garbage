import VerifiedGarbage.Proof.MlKem.Arith

/-!
# ML-KEM: bit arrays as numbers, for every target

Untrusted: everything here is checked by Lean. `ByteEncode_d` and
`ByteDecode_d` (Algorithms 5 and 6) go through arrays of bits
(`BitsToBytes`, `BytesToBits`, Algorithms 3 and 4). Here they are
restated without bits: a list of integers less than `2ʷ` is the digits of a
little-endian number in base `2ʷ` (`digits w`), and

* byte `k` of `ByteEncode_d(F)` is byte `k` of the number whose base-`2ᵈ`
  digits are `F` (`byteEncode_getElem`);
* `ByteDecode_d(B)[i]` is base-`2ᵈ` digit `i` of the number whose bytes are
  `B`, reduced modulo `m` (`byteDecode_getElem`);
* both group by group: `d · c = 8 · b` bits are `c` integers or `b` bytes
  (`byteEncode_group`, `byteDecode_group`), from which `Encode.lean`
  derives the formulas an implementation computes.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## Numbers from digits -/

/-- The little-endian number whose base-`2ʷ` digits are `L`:
`L[0] + 2ʷ · L[1] + 2²ʷ · L[2] + ⋯`. -/
def digits (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: L => a + 2 ^ w * digits w L

theorem digits_nil (w : Nat) : digits w [] = 0 := rfl

theorem digits_cons (w a : Nat) (L : List Nat) : digits w (a :: L) = a + 2 ^ w * digits w L := rfl

/-- `(a + 2ʷ · D) / 2ʷ = D` for a digit `a < 2ʷ`. -/
theorem add_pow_mul_div {w a : Nat} (ha : a < 2 ^ w) (D : Nat) : (a + 2 ^ w * D) / 2 ^ w = D := by
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt ha, Nat.zero_add]

theorem digits_lt {w : Nat} : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → digits w L < 2 ^ (w * L.length)
  | [], _ => by simp [digits]
  | a :: L, h => by
    have ha := h a (List.mem_cons_self ..)
    have hL := digits_lt (L := L) fun b hb => h b (List.mem_cons_of_mem _ hb)
    have h1 : 2 ^ w * digits w L + 2 ^ w ≤ 2 ^ w * 2 ^ (w * L.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hL
    rw [digits_cons, List.length_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * L.length))]
    omega

/-- The low `c` digits. -/
theorem digits_mod {w : Nat} : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → ∀ c,
    digits w L % 2 ^ (w * c) = digits w (L.take c)
  | [], _, c => by simp [digits]
  | a :: L, h, 0 => by simp [Nat.mod_one, digits]
  | a :: L, h, c + 1 => by
    have ha := h a (List.mem_cons_self ..)
    rw [List.take_succ_cons, digits_cons, digits_cons, Nat.mul_succ, Nat.pow_add,
      Nat.mul_comm (2 ^ (w * c)), Nat.mod_mul, add_pow_mul_div ha,
      digits_mod (fun b hb => h b (List.mem_cons_of_mem _ hb)) c, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ha]

/-- The digits from `s` on. -/
theorem digits_div {w : Nat} : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → ∀ s,
    digits w L / 2 ^ (w * s) = digits w (L.drop s)
  | L, _, 0 => by simp
  | [], _, s + 1 => by simp [digits]
  | a :: L, h, s + 1 => by
    have ha := h a (List.mem_cons_self ..)
    rw [List.drop_succ_cons, digits_cons, Nat.mul_succ, Nat.pow_add, Nat.mul_comm (2 ^ (w * s)),
      ← Nat.div_div_eq_div_mul, add_pow_mul_div ha,
      digits_div (fun b hb => h b (List.mem_cons_of_mem _ hb)) s]

/-- Digits `s … s + c - 1`. -/
theorem digits_chunk {w : Nat} {L : List Nat} (h : ∀ a ∈ L, a < 2 ^ w) (s c : Nat) :
    digits w L / 2 ^ (w * s) % 2 ^ (w * c) = digits w ((L.drop s).take c) := by
  rw [digits_div h, digits_mod (fun a ha => h a (List.mem_of_mem_drop ha))]

/-- Bit `p` of the number is bit `p mod w` of digit `⌊p / w⌋`. -/
theorem digits_bit {w : Nat} (hw : 0 < w) : ∀ {L : List Nat}, (∀ a ∈ L, a < 2 ^ w) → ∀ p,
    digits w L / 2 ^ p % 2 = L.getD (p / w) 0 / 2 ^ (p % w) % 2
  | [], _, p => by simp [digits]
  | a :: L, h, p => by
    have ha := h a (List.mem_cons_self ..)
    rw [digits_cons]
    by_cases hp : p < w
    · rw [Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp, List.getD_cons_zero]
      have e : 2 ^ w = 2 ^ p * 2 ^ (w - p) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos p)]
      have e2 : 2 ^ (w - p) = 2 * 2 ^ (w - p - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      rw [e2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
    · have e : 2 ^ p = 2 ^ w * 2 ^ (p - w) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, ← Nat.div_div_eq_div_mul, add_pow_mul_div ha,
        digits_bit hw (fun b hb => h b (List.mem_cons_of_mem _ hb)) (p - w),
        show p / w = (p - w) / w + 1 from Nat.div_eq_sub_div hw (by omega), List.getD_cons_succ,
        show p % w = (p - w) % w from Nat.mod_eq_sub_mod (by omega)]

/-- The sum of the bits `j < w` of `M`, each times `2ʲ`, is `M mod 2ʷ`. -/
theorem sum_bits (M : Nat) : ∀ w, ((List.range w).map fun j => M / 2 ^ j % 2 * 2 ^ j).sum = M % 2 ^ w
  | 0 => by simp [Nat.mod_one]
  | w + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_bits M w, Nat.mod_pow_succ]
    simp [Nat.mul_comm]

/-- `(X mod 2ᵃ) / 2ᵇ mod 2ᶜ = X / 2ᵇ mod 2ᶜ` when `b + c ≤ a`. -/
theorem mod_pow_div_mod (X : Nat) {a b c : Nat} (h : b + c ≤ a) :
    X % 2 ^ a / 2 ^ b % 2 ^ c = X / 2 ^ b % 2 ^ c := by
  rw [show a = b + (a - b) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- A byte is determined modulo 256. -/
theorem ofNat8_mod (x : Nat) : BitVec.ofNat 8 (x % 256) = BitVec.ofNat 8 x :=
  BitVec.eq_of_toNat_eq (by simp only [BitVec.toNat_ofNat]; omega)

theorem ofNat8_eq {x y : Nat} (h : x % 256 = y % 256) : BitVec.ofNat 8 x = BitVec.ofNat 8 y := by
  rw [← ofNat8_mod x, h, ofNat8_mod]

/-! ## Lists of lists -/

theorem getElem?_flatMap_const {α β : Type} (f : α → List β) {d : Nat} (hd : 0 < d) :
    ∀ (L : List α), (∀ a ∈ L, (f a).length = d) → ∀ j,
      (L.flatMap f)[j]? = L[j / d]?.bind fun a => (f a)[j % d]?
  | [], _, j => by simp
  | a :: L, hf, j => by
    have ha := hf a (List.mem_cons_self ..)
    rw [List.flatMap_cons]
    by_cases hj : j < d
    · rw [List.getElem?_append_left (by rw [ha]; exact hj), Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
      rfl
    · rw [List.getElem?_append_right (by rw [ha]; omega), ha,
        getElem?_flatMap_const f hd L (fun b hb => hf b (List.mem_cons_of_mem _ hb)) (j - d),
        show j / d = (j - d) / d + 1 from Nat.div_eq_sub_div hd (by omega),
        show j % d = (j - d) % d from Nat.mod_eq_sub_mod (by omega), List.getElem?_cons_succ]

theorem length_flatMap_const {α β : Type} (f : α → List β) {d : Nat} (hf : ∀ a, (f a).length = d) :
    ∀ L : List α, (L.flatMap f).length = d * L.length
  | [] => rfl
  | a :: L => by
    rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f hf L, List.length_cons,
      Nat.mul_succ, Nat.add_comm]

private theorem toNat_decide (x : Nat) : (decide (x % 2 = 1)).toNat = x % 2 := by
  cases Nat.mod_two_eq_zero_or_one x with
  | inl h => rw [h]; rfl
  | inr h => rw [h]; rfl

/-- Bit `p` of the concatenated bits of `L`: bit `p mod d` of `L[⌊p / d⌋]`,
as a number (0 past the end). -/
private theorem bits_getD {d : Nat} (hd : 0 < d) (L : List Nat) (p : Nat) :
    ((L.flatMap fun a => (List.range d).map fun j => decide (a / 2 ^ j % 2 = 1)).toArray.getD p
      false).toNat = L.getD (p / d) 0 / 2 ^ (p % d) % 2 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    getElem?_flatMap_const _ (d := d) hd _ (fun a _ => by simp), List.getD_eq_getElem?_getD]
  cases h : L[p / d]? with
  | none => simp
  | some a =>
    simp only [Option.bind_some, Option.getD_some,
      List.getElem?_map, List.getElem?_range (Nat.mod_lt _ hd), Option.map_some]
    exact toNat_decide _

/-- Bit `p` of `BytesToBits(B)`, as a number: bit `p mod 8` of byte
`⌊p / 8⌋` (0 past the end). -/
theorem bytesToBits_getD (B : List Byte) (p : Nat) :
    ((bytesToBits B).getD p false).toNat = (B.getD (p / 8) 0).toNat / 2 ^ (p % 8) % 2 := by
  simp only [bytesToBits]
  rw [show (B.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)) =
    (B.map (·.toNat)).flatMap (fun a => (List.range 8).map fun j => decide (a / 2 ^ j % 2 = 1)) by
      simp [List.flatMap_map], bits_getD (by decide) (B.map (·.toNat)) p]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases B[p / 8]? <;> rfl

/-! ## ByteEncode and ByteDecode -/

theorem byteEncode_length (d : Nat) (F : Vector Nat n) : (byteEncode d F).length = 32 * d := by
  simp only [byteEncode, bitsToBytes, List.length_map, List.length_range, List.size_toArray]
  rw [length_flatMap_const (d := d) _ (fun a => by simp) F.toList, Vector.length_toList, n_eq]
  omega

/-- Byte `k` of `ByteEncode_d(F)` is byte `k` of the number whose base-`2ᵈ`
digits are `F`. -/
theorem byteEncode_getElem {d : Nat} (hd : 0 < d) {F : Vector Nat n} (hF : ∀ a ∈ F.toList, a < 2 ^ d)
    {k : Nat} (hk : k < 32 * d) :
    (byteEncode d F)[k]! = BitVec.ofNat 8 (digits d F.toList / 2 ^ (8 * k)) := by
  rw [getElem!_pos _ _ (by rw [byteEncode_length]; exact hk)]
  simp only [byteEncode, bitsToBytes, List.getElem_map, List.getElem_range]
  rw [← ofNat8_mod (digits d F.toList / 2 ^ (8 * k))]
  refine congrArg (BitVec.ofNat 8) ?_
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← sum_bits (digits d F.toList / 2 ^ (8 * k)) 8]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  rw [bits_getD hd F.toList (8 * k + j), ← digits_bit hd hF, Nat.div_div_eq_div_mul, ← Nat.pow_add]

/-- Byte `b · g + j` of `ByteEncode_d(F)` when each group of `b` bytes holds
`c` integers (`d · c = 8 · b`): byte `j` of the number whose base-`2ᵈ`
digits are the `c` integers of group `g`. -/
theorem byteEncode_group {d c b : Nat} (hd : 0 < d) (hdc : d * c = 8 * b) {F : Vector Nat n}
    (hF : ∀ a ∈ F.toList, a < 2 ^ d) {g j : Nat} (hj : j < b) (hk : b * g + j < 32 * d) :
    (byteEncode d F)[b * g + j]! =
      BitVec.ofNat 8 (digits d ((F.toList.drop (c * g)).take c) / 2 ^ (8 * j)) := by
  have hx : 8 * (b * g + j) = d * (c * g) + 8 * j := by
    rw [Nat.mul_add, ← Nat.mul_assoc, ← Nat.mul_assoc, hdc]
  rw [byteEncode_getElem hd hF hk, hx, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    ← ofNat8_mod (_ / 2 ^ (8 * j)), ← ofNat8_mod (digits d _ / 2 ^ (8 * j)), ← digits_chunk hF,
    show (256 : Nat) = 2 ^ 8 from rfl, mod_pow_div_mod _ (show 8 * j + 8 ≤ d * c by omega)]

theorem map_bytes_lt (B : List Byte) : ∀ a ∈ B.map (·.toNat), a < 2 ^ 8 := by
  intro a ha
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
  exact x.isLt

/-- `ByteDecode_d(B)[i]` is base-`2ᵈ` digit `i` of the number whose bytes
are `B`, reduced modulo `m` (`2ᵈ`, or `q` for `d = 12`). -/
theorem byteDecode_getElem (d : Nat) (B : List Byte) {i : Nat} (hi : i < n) :
    (byteDecode d B)[i]! =
      digits 8 (B.map (·.toNat)) / 2 ^ (d * i) % 2 ^ d % (if d < 12 then 2 ^ d else q) := by
  rw [getElem!_pos (byteDecode d B) i hi]
  simp only [byteDecode, Vector.getElem_ofFn]
  refine congrArg (· % _) ?_
  rw [← sum_bits _ d]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  simp only [bytesToBits]
  rw [show (B.flatMap fun c => (List.range 8).map fun j => decide (c.toNat / 2 ^ j % 2 = 1)) =
    (B.map (·.toNat)).flatMap (fun a => (List.range 8).map fun j => decide (a / 2 ^ j % 2 = 1)) by
      simp [List.flatMap_map], bits_getD (by decide) (B.map (·.toNat)) (i * d + j),
    ← digits_bit (by decide) (map_bytes_lt B), Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_comm d i]

/-- `ByteDecode_d(B)[c · g + e]` when each group of `b` bytes holds `c`
integers (`d · c = 8 · b`): digit `e` of the number whose bytes are the `b`
bytes of group `g`. -/
theorem byteDecode_group {d c b : Nat} (hdc : d * c = 8 * b) (B : List Byte) {g e : Nat} (he : e < c)
    (hi : c * g + e < n) :
    (byteDecode d B)[c * g + e]! =
      digits 8 (((B.drop (b * g)).take b).map (·.toNat)) / 2 ^ (d * e) % 2 ^ d %
        (if d < 12 then 2 ^ d else q) := by
  have hx : d * (c * g + e) = 8 * (b * g) + d * e := by
    rw [Nat.mul_add, ← Nat.mul_assoc, hdc, Nat.mul_assoc]
  have hde : d * e + d ≤ 8 * b := by
    rw [← hdc, show d * e + d = d * (e + 1) by rw [Nat.mul_succ]]; exact Nat.mul_le_mul_left _ he
  rw [byteDecode_getElem d B hi, List.map_take, List.map_drop, ← digits_chunk (map_bytes_lt B),
    mod_pow_div_mod _ hde, Nat.div_div_eq_div_mul, ← Nat.pow_add, hx]

/-! ## Explicit groups -/

/-- `c` consecutive elements from `s`, when they are in the list. -/
theorem take_drop_eq {α : Type} (L : List α) (x : α) {s c : Nat} (h : s + c ≤ L.length) :
    (L.drop s).take c = (List.range c).map fun j => L.getD (s + j) x := by
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]

/-- A list of `c · N` elements is the concatenation of `N` lists of `c`
elements if each element is. -/
theorem eq_flatMap {α : Type} [Inhabited α] {L : List α} {g : Nat → List α} {c N : Nat} (hc : 0 < c)
    (hg : ∀ i < N, (g i).length = c) (hL : L.length = c * N)
    (h : ∀ i < N, ∀ j < c, L[c * i + j]! = (g i)[j]!) : L = (List.range N).flatMap g := by
  refine List.ext_getElem? fun k => ?_
  rw [getElem?_flatMap_const g hc _ fun i hi => hg i (List.mem_range.mp hi)]
  by_cases hk : k < c * N
  · have hq : k / c < N := Nat.div_lt_of_lt_mul hk
    have hr : k % c < c := Nat.mod_lt _ hc
    rw [List.getElem?_range hq, Option.bind_some, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by rw [hg _ hq]; exact hr)]
    have := h (k / c) hq (k % c) hr
    rw [Nat.div_add_mod, getElem!_pos L k (by omega),
      getElem!_pos (g (k / c)) _ (by rw [hg _ hq]; exact hr)] at this
    rw [this]
  · rw [List.getElem?_eq_none (by omega : L.length ≤ k),
      List.getElem?_eq_none (l := List.range N) (by
        rw [List.length_range]; exact (Nat.le_div_iff_mul_le hc).mpr (by rw [Nat.mul_comm]; omega)),
      Option.bind_none]

end VG.Proof.MlKem
