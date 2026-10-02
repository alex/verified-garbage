import VerifiedGarbage.Proof.MlKem.Bits
import VerifiedGarbage.Proof.MlKem.Compress

/-!
# ML-KEM: encoding, decoding and sampling byte by byte, for every target

The functions of §4.2 on bytes, restated group by group as the arithmetic an
implementation does (with `Bits.lean`), for reduced inputs:

* `ByteEncode₁₂`: 2 coefficients `f₀, f₁` per 3 bytes,
  `[f₀ mod 256, ⌊f₀/256⌋ + 16(f₁ mod 16), ⌊f₁/16⌋]` (`encode12_eq`);
  `ByteDecode₁₂`: `B₀ + 256(B₁ mod 16)` and `⌊B₁/16⌋ + 16B₂`, reduced modulo `q`
  (`decode12_even`, `decode12_odd`);
* `ByteEncode_d ∘ Compress_d` for any `d`, group by group
  (`compressEncode_group`), and for `d` = 1 (8 coefficients per byte), 4 (2
  per byte) and 10 (4 per 5 bytes) (`compressEncode1`, `compressEncode4`,
  `compressEncode10_*`), and `Decompress_d ∘ ByteDecode_d`
  (`decodeDecompress_group`, `decodeDecompress1`, `…4_*`, `…10_*`);
* `SamplePolyCBD₂`: coefficient `i` from nibble `i` of `B`
  (`samplePolyCBD2_get`, `samplePolyCBD2_val`).

Byte `k` of a list `B` is written `B.getD k 0`, which `bytesAt_getD`
(`Mem.lean`) reads from memory.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-! ## Lists of coefficients -/

theorem map_toList_length (f : Poly) (g : Zq → Nat) : (f.map g).toList.length = 256 := by simp

theorem map_toList_getD (f : Poly) (g : Zq → Nat) {i : Nat} (hi : i < 256) :
    (f.map g).toList.getD i 0 = g f[i]! := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; exact hi), Option.getD_some,
    Vector.getElem_toList, Vector.getElem_map, getElem!_eq _ hi]

theorem map_toList_lt (f : Poly) {g : Zq → Nat} {d : Nat} (hg : ∀ x, g x < 2 ^ d) :
    ∀ a ∈ (f.map g).toList, a < 2 ^ d := by
  intro a ha
  rw [Vector.toList_map] at ha
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
  exact hg x

theorem val_lt_4096 (x : Zq) : x.val < 2 ^ 12 := by have := val_lt x; omega

theorem bytes_map_take_drop (B : List Byte) {s c : Nat} (h : s + c ≤ B.length) :
    ((B.drop s).take c).map (·.toNat) = (List.range c).map fun j => (B.getD (s + j) 0).toNat := by
  rw [take_drop_eq B 0 h, List.map_map]; rfl

theorem range2 : List.range 2 = [0, 1] := rfl
theorem range3 : List.range 3 = [0, 1, 2] := rfl
theorem range4 : List.range 4 = [0, 1, 2, 3] := rfl
theorem range5 : List.range 5 = [0, 1, 2, 3, 4] := rfl
theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

/-- The digits of an explicit list. -/
theorem digits_map_range {w c : Nat} (g : Nat → Nat) :
    digits w ((List.range (c + 1)).map g) = g 0 + 2 ^ w * digits w ((List.range c).map (g ∘ (· + 1))) := by
  rw [List.range_succ_eq_map, List.map_cons, List.map_map, digits_cons]

theorem byte_lt (b : Byte) : b.toNat < 256 := b.isLt

/-! ## ByteEncode₁₂ and ByteDecode₁₂ -/

theorem encode12_length (f : Poly) : (encode12 f).length = 384 := byteEncode_length 12 _

/-- The three bytes of group `i` of `ByteEncode₁₂(f)`, as bytes of
`f[2i] + 2¹² · f[2i + 1]`. -/
theorem encode12_group (f : Poly) {i j : Nat} (hi : i < 128) (hj : j < 3) :
    (encode12 f)[3 * i + j]! =
      BitVec.ofNat 8 (((f[2 * i]!).val + 4096 * (f[2 * i + 1]!).val) / 2 ^ (8 * j)) := by
  rw [encode12, byteEncode_group (d := 12) (c := 2) (b := 3) (by decide) (by decide) (map_toList_lt f val_lt_4096) hj
    (by omega), take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  simp only [range2, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    map_toList_getD f _ (show 2 * i < 256 by omega), map_toList_getD f _ (show 2 * i + 1 < 256 by omega)]
  rfl

theorem encode12_byte0 (f : Poly) {i : Nat} (hi : i < 128) :
    (encode12 f)[3 * i]! = BitVec.ofNat 8 ((f[2 * i]!).val % 256) := by
  have h := encode12_group f hi (j := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  clear h
  exact ofNat8_eq (by have := val_lt f[2 * i]!; have := val_lt f[2 * i + 1]!; omega)

theorem encode12_byte1 (f : Poly) {i : Nat} (hi : i < 128) :
    (encode12 f)[3 * i + 1]! =
      BitVec.ofNat 8 ((f[2 * i]!).val / 256 + 16 * ((f[2 * i + 1]!).val % 16)) := by
  rw [encode12_group f hi (by decide)]
  exact ofNat8_eq (by have := val_lt f[2 * i]!; have := val_lt f[2 * i + 1]!; omega)

theorem encode12_byte2 (f : Poly) {i : Nat} (hi : i < 128) :
    (encode12 f)[3 * i + 2]! = BitVec.ofNat 8 ((f[2 * i + 1]!).val / 16) := by
  rw [encode12_group f hi (by decide)]
  exact ofNat8_eq (by have := val_lt f[2 * i]!; have := val_lt f[2 * i + 1]!; omega)

/-- `ByteEncode₁₂(f)`, 3 bytes per pair of coefficients. -/
theorem encode12_eq (f : Poly) :
    encode12 f = (List.range 128).flatMap fun i =>
      [BitVec.ofNat 8 ((f[2 * i]!).val % 256),
        BitVec.ofNat 8 ((f[2 * i]!).val / 256 + 16 * ((f[2 * i + 1]!).val % 16)),
        BitVec.ofNat 8 ((f[2 * i + 1]!).val / 16)] := by
  refine eq_flatMap (c := 3) (N := 128) (by decide) (fun _ _ => rfl) (encode12_length f) fun i hi j hj => ?_
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
  · rw [Nat.add_zero, encode12_byte0 f hi]; rfl
  · rw [encode12_byte1 f hi]; rfl
  · rw [encode12_byte2 f hi]; rfl

theorem decode12_get (B : List Byte) {k : Nat} (hk : k < n) :
    (decode12 B)[k]! = ofNat ((byteDecode 12 B)[k]!) := by
  rw [getElem!_eq _ hk, getElem!_pos (byteDecode 12 B) k hk]
  simp only [decode12, Vector.getElem_map]

/-- The integer that coefficients `2i` and `2i + 1` of `ByteDecode₁₂` are
the 12-bit fields of. -/
private theorem decode12_group (B : List Byte) (hB : B.length = 384) {i e : Nat} (hi : i < 128)
    (he : e < 2) :
    (decode12 B)[2 * i + e]! = ofNat (((B.getD (3 * i) 0).toNat + 256 * (B.getD (3 * i + 1) 0).toNat +
      65536 * (B.getD (3 * i + 2) 0).toNat) / 2 ^ (12 * e) % 4096) := by
  rw [decode12_get B (by rw [n_eq]; omega), byteDecode_group (c := 2) (b := 3) (by decide) B he
    (by rw [n_eq]; omega), bytes_map_take_drop B (by omega)]
  simp only [range3, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.lt_irrefl, ↓reduceIte, ofNat_mod]
  refine congrArg ofNat (congrArg (· % 4096) (congrArg (· / 2 ^ (12 * e)) ?_))
  omega

/-- Coefficient `2i` of `ByteDecode₁₂(B)`: `B[3i] + 256 · (B[3i + 1] mod 16)`,
modulo `q`. -/
theorem decode12_even (B : List Byte) (hB : B.length = 384) {i : Nat} (hi : i < 128) :
    (decode12 B)[2 * i]! =
      ofNat ((B.getD (3 * i) 0).toNat + 256 * ((B.getD (3 * i + 1) 0).toNat % 16)) := by
  have h := decode12_group B hB hi (e := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  clear h
  refine congrArg ofNat ?_
  have := byte_lt (B.getD (3 * i) 0); have := byte_lt (B.getD (3 * i + 1) 0)
  have := byte_lt (B.getD (3 * i + 2) 0)
  omega

/-- Coefficient `2i + 1` of `ByteDecode₁₂(B)`: `⌊B[3i + 1] / 16⌋ + 16 · B[3i + 2]`,
modulo `q`. -/
theorem decode12_odd (B : List Byte) (hB : B.length = 384) {i : Nat} (hi : i < 128) :
    (decode12 B)[2 * i + 1]! =
      ofNat ((B.getD (3 * i + 1) 0).toNat / 16 + 16 * (B.getD (3 * i + 2) 0).toNat) := by
  rw [decode12_group B hB hi (by decide)]
  refine congrArg ofNat ?_
  have := byte_lt (B.getD (3 * i) 0); have := byte_lt (B.getD (3 * i + 1) 0)
  have := byte_lt (B.getD (3 * i + 2) 0)
  omega

/-! ## ByteEncode_d ∘ Compress_d -/

theorem compressEncode_length (d : Nat) (f : Poly) : (compressEncode d f).length = 32 * d :=
  byteEncode_length d _

/-- Byte `b·g + j` of `ByteEncode_d(Compress_d(f))`, when each group of `b`
bytes holds `c` coefficients (`d · c = 8 · b`): byte `j` of the number whose
base-`2ᵈ` digits are the compressed coefficients `c·g … c·g + c - 1`. -/
theorem compressEncode_group {d c b : Nat} (hd : 0 < d) (hdc : d * c = 8 * b) (f : Poly) {g j : Nat}
    (hg : c * g + c ≤ 256) (hj : j < b) :
    (compressEncode d f)[b * g + j]! =
      BitVec.ofNat 8 (digits d ((List.range c).map fun i => compress d f[c * g + i]!) / 2 ^ (8 * j)) := by
  have h₁ : d * (c * (g + 1)) ≤ d * 256 := Nat.mul_le_mul_left d (by rw [Nat.mul_succ]; exact hg)
  have h₂ : d * (c * (g + 1)) = 8 * (b * g + b) := by rw [← Nat.mul_assoc, hdc, Nat.mul_assoc, Nat.mul_succ]
  rw [compressEncode, byteEncode_group hd hdc (map_toList_lt f (compress_lt d)) hj (by omega),
    take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  refine congrArg (fun L => BitVec.ofNat 8 (digits d L / 2 ^ (8 * j))) (List.map_congr_left fun i hi => ?_)
  exact map_toList_getD f _ (by have := List.mem_range.mp hi; omega)

/-- Byte `k` of `ByteEncode₁(Compress₁(f))`: the compressed coefficients
`8k … 8k + 7` as its bits. -/
theorem compressEncode1 (f : Poly) {k : Nat} (hk : k < 32) :
    (compressEncode 1 f)[k]! = BitVec.ofNat 8 (compress 1 f[8 * k]! + 2 * compress 1 f[8 * k + 1]! +
      4 * compress 1 f[8 * k + 2]! + 8 * compress 1 f[8 * k + 3]! + 16 * compress 1 f[8 * k + 4]! +
      32 * compress 1 f[8 * k + 5]! + 64 * compress 1 f[8 * k + 6]! +
      128 * compress 1 f[8 * k + 7]!) := by
  have h := compressEncode_group (d := 1) (c := 8) (b := 1) (g := k) (j := 0) (by decide) (by decide) f (by omega)
    (by decide)
  rw [show 1 * k + 0 = k by omega] at h
  rw [h]
  clear h
  simp only [range8, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  refine congrArg (BitVec.ofNat 8) ?_
  omega

/-- Byte `k` of `ByteEncode₄(Compress₄(f))`: compressed coefficients `2k`
and `2k + 1`. -/
theorem compressEncode4 (f : Poly) {k : Nat} (hk : k < 128) :
    (compressEncode 4 f)[k]! = BitVec.ofNat 8 (compress 4 f[2 * k]! + 16 * compress 4 f[2 * k + 1]!) := by
  have h := compressEncode_group (d := 4) (c := 2) (b := 1) (g := k) (j := 0) (by decide) (by decide) f (by omega)
    (by decide)
  rw [show 1 * k + 0 = k by omega] at h
  rw [h]
  clear h
  simp only [range2, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.mul_zero, Nat.pow_zero, Nat.div_one]

/-- Byte `5g + j` of `ByteEncode₁₀(Compress₁₀(f))`: byte `j` of the 40-bit
number of the compressed coefficients `4g … 4g + 3`. -/
private theorem compressEncode10_group (f : Poly) {g j : Nat} (hg : g < 64) (hj : j < 5) :
    (compressEncode 10 f)[5 * g + j]! = BitVec.ofNat 8 ((compress 10 f[4 * g]! +
      1024 * compress 10 f[4 * g + 1]! + 1048576 * compress 10 f[4 * g + 2]! +
      1073741824 * compress 10 f[4 * g + 3]!) / 2 ^ (8 * j)) := by
  rw [compressEncode_group (c := 4) (by decide) (by decide) f (by omega) hj]
  simp only [range4, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  refine congrArg (BitVec.ofNat 8) (congrArg (· / 2 ^ (8 * j)) ?_)
  omega

section
variable (f : Poly) {g : Nat} (hg : g < 64)
include hg

omit hg in
private theorem c10_lt (i : Nat) : compress 10 f[i]! < 1024 := compress_lt 10 _

theorem compressEncode10_0 :
    (compressEncode 10 f)[5 * g]! = BitVec.ofNat 8 (compress 10 f[4 * g]! % 256) := by
  have h := compressEncode10_group f hg (j := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  clear h
  have := c10_lt f (4 * g); have := c10_lt f (4 * g + 1); have := c10_lt f (4 * g + 2)
  have := c10_lt f (4 * g + 3)
  exact ofNat8_eq (by omega)

theorem compressEncode10_1 :
    (compressEncode 10 f)[5 * g + 1]! =
      BitVec.ofNat 8 (compress 10 f[4 * g]! / 256 + 4 * (compress 10 f[4 * g + 1]! % 64)) := by
  rw [compressEncode10_group f hg (by decide)]
  have := c10_lt f (4 * g); have := c10_lt f (4 * g + 1); have := c10_lt f (4 * g + 2)
  have := c10_lt f (4 * g + 3)
  exact ofNat8_eq (by omega)

theorem compressEncode10_2 :
    (compressEncode 10 f)[5 * g + 2]! =
      BitVec.ofNat 8 (compress 10 f[4 * g + 1]! / 64 + 16 * (compress 10 f[4 * g + 2]! % 16)) := by
  rw [compressEncode10_group f hg (by decide)]
  have := c10_lt f (4 * g); have := c10_lt f (4 * g + 1); have := c10_lt f (4 * g + 2)
  have := c10_lt f (4 * g + 3)
  exact ofNat8_eq (by omega)

theorem compressEncode10_3 :
    (compressEncode 10 f)[5 * g + 3]! =
      BitVec.ofNat 8 (compress 10 f[4 * g + 2]! / 16 + 64 * (compress 10 f[4 * g + 3]! % 4)) := by
  rw [compressEncode10_group f hg (by decide)]
  have := c10_lt f (4 * g); have := c10_lt f (4 * g + 1); have := c10_lt f (4 * g + 2)
  have := c10_lt f (4 * g + 3)
  exact ofNat8_eq (by omega)

theorem compressEncode10_4 :
    (compressEncode 10 f)[5 * g + 4]! = BitVec.ofNat 8 (compress 10 f[4 * g + 3]! / 4) := by
  rw [compressEncode10_group f hg (by decide)]
  have := c10_lt f (4 * g); have := c10_lt f (4 * g + 1); have := c10_lt f (4 * g + 2)
  have := c10_lt f (4 * g + 3)
  exact ofNat8_eq (by omega)

end

/-! ## Decompress_d ∘ ByteDecode_d -/

theorem decodeDecompress_get (d : Nat) (B : List Byte) {k : Nat} (hk : k < n) :
    (decodeDecompress d B)[k]! = decompress d ((byteDecode d B)[k]!) := by
  rw [getElem!_eq _ hk, getElem!_pos (byteDecode d B) k hk]
  simp only [decodeDecompress, Vector.getElem_map]

/-- Coefficient `c·g + e` of `Decompress_d(ByteDecode_d(B))`, when each group
of `b` bytes holds `c` coefficients (`d · c = 8 · b`): `d`-bit field `e` of
the number whose bytes are `B[b·g … b·g + b - 1]`, decompressed. -/
theorem decodeDecompress_group {d c b : Nat} (hd : d < 12) (hdc : d * c = 8 * b) (B : List Byte) {g e : Nat}
    (hB : b * g + b ≤ B.length) (he : e < c) (hi : c * g + e < n) :
    (decodeDecompress d B)[c * g + e]! =
      decompress d (digits 8 ((List.range b).map fun i => (B.getD (b * g + i) 0).toNat) / 2 ^ (d * e) % 2 ^ d) := by
  rw [decodeDecompress_get d B hi, byteDecode_group hdc B he hi, bytes_map_take_drop B hB]
  simp only [hd, ↓reduceIte, Nat.mod_mod]

/-- Coefficient `i` of `Decompress₁(ByteDecode₁(B))`: bit `i mod 8` of byte
`⌊i / 8⌋`, decompressed. -/
theorem decodeDecompress1 (B : List Byte) {i : Nat} (hi : i < n) :
    (decodeDecompress 1 B)[i]! = decompress 1 ((B.getD (i / 8) 0).toNat / 2 ^ (i % 8) % 2) := by
  rw [decodeDecompress_get 1 B hi, byteDecode_getElem 1 B hi]
  simp only [Nat.pow_one, Nat.one_mul, Nat.reduceLT, ↓reduceIte, Nat.mod_mod]
  rw [digits_bit (by decide) (map_bytes_lt B)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases B[i / 8]? <;> rfl

private theorem decodeDecompress4_group (B : List Byte) (hB : B.length = 128) {i e : Nat}
    (hi : i < 128) (he : e < 2) :
    (decodeDecompress 4 B)[2 * i + e]! = decompress 4 ((B.getD i 0).toNat / 2 ^ (4 * e) % 16) := by
  rw [decodeDecompress_group (c := 2) (b := 1) (by decide) (by decide) B (by omega) he (by rw [n_eq]; omega)]
  simp only [List.range_one, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.mul_zero, Nat.one_mul]

/-- Coefficient `2i` of `Decompress₄(ByteDecode₄(B))`: the low nibble of
`B[i]`, decompressed. -/
theorem decodeDecompress4_even (B : List Byte) (hB : B.length = 128) {i : Nat} (hi : i < 128) :
    (decodeDecompress 4 B)[2 * i]! = decompress 4 ((B.getD i 0).toNat % 16) := by
  have h := decodeDecompress4_group B hB hi (e := 0) (by decide)
  rw [Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.div_one] at h
  exact h

/-- Coefficient `2i + 1` of `Decompress₄(ByteDecode₄(B))`: the high nibble
of `B[i]`, decompressed. -/
theorem decodeDecompress4_odd (B : List Byte) (hB : B.length = 128) {i : Nat} (hi : i < 128) :
    (decodeDecompress 4 B)[2 * i + 1]! = decompress 4 ((B.getD i 0).toNat / 16) := by
  rw [decodeDecompress4_group B hB hi (by decide)]
  refine congrArg (decompress 4) ?_
  have := byte_lt (B.getD i 0)
  omega

/-- The 40-bit number of bytes `5g … 5g + 4`. -/
private theorem decodeDecompress10_group (B : List Byte) (hB : B.length = 320) {g e : Nat}
    (hg : g < 64) (he : e < 4) :
    (decodeDecompress 10 B)[4 * g + e]! = decompress 10 (((B.getD (5 * g) 0).toNat +
      256 * (B.getD (5 * g + 1) 0).toNat + 65536 * (B.getD (5 * g + 2) 0).toNat +
      16777216 * (B.getD (5 * g + 3) 0).toNat + 4294967296 * (B.getD (5 * g + 4) 0).toNat) /
        2 ^ (10 * e) % 1024) := by
  rw [decodeDecompress_group (c := 4) (b := 5) (by decide) (by decide) B (by omega) he (by rw [n_eq]; omega)]
  simp only [range5, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  refine congrArg (decompress 10) (congrArg (· % 1024) (congrArg (· / 2 ^ (10 * e)) ?_))
  omega

section
variable (B : List Byte) (hB : B.length = 320) {g : Nat} (hg : g < 64)
include hB hg

omit hB hg in
private theorem bytes5_lt : (B.getD (5 * g) 0).toNat < 256 ∧ (B.getD (5 * g + 1) 0).toNat < 256 ∧
    (B.getD (5 * g + 2) 0).toNat < 256 ∧ (B.getD (5 * g + 3) 0).toNat < 256 ∧
    (B.getD (5 * g + 4) 0).toNat < 256 :=
  ⟨byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _⟩

/-- Coefficient `4g` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_0 :
    (decodeDecompress 10 B)[4 * g]! = decompress 10 ((B.getD (5 * g) 0).toNat +
      256 * ((B.getD (5 * g + 1) 0).toNat % 4)) := by
  have h := decodeDecompress10_group B hB hg (e := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  clear h
  refine congrArg (decompress 10) ?_
  have := bytes5_lt B (g := g)
  omega

/-- Coefficient `4g + 1` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_1 :
    (decodeDecompress 10 B)[4 * g + 1]! = decompress 10 ((B.getD (5 * g + 1) 0).toNat / 4 +
      64 * ((B.getD (5 * g + 2) 0).toNat % 16)) := by
  rw [decodeDecompress10_group B hB hg (by decide)]
  refine congrArg (decompress 10) ?_
  have := bytes5_lt B (g := g)
  omega

/-- Coefficient `4g + 2` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_2 :
    (decodeDecompress 10 B)[4 * g + 2]! = decompress 10 ((B.getD (5 * g + 2) 0).toNat / 16 +
      16 * ((B.getD (5 * g + 3) 0).toNat % 64)) := by
  rw [decodeDecompress10_group B hB hg (by decide)]
  refine congrArg (decompress 10) ?_
  have := bytes5_lt B (g := g)
  omega

/-- Coefficient `4g + 3` of `Decompress₁₀(ByteDecode₁₀(B))`. -/
theorem decodeDecompress10_3 :
    (decodeDecompress 10 B)[4 * g + 3]! = decompress 10 ((B.getD (5 * g + 3) 0).toNat / 64 +
      4 * (B.getD (5 * g + 4) 0).toNat) := by
  rw [decodeDecompress10_group B hB hg (by decide)]
  refine congrArg (decompress 10) ?_
  have := bytes5_lt B (g := g)
  omega

end

/-! ## SamplePolyCBD₂ -/

/-- `x` of `SamplePolyCBD₂` from the nibble `v`: its bits 0 and 1. -/
def cbdX (v : Nat) : Nat := v % 2 + v / 2 % 2

/-- `y` of `SamplePolyCBD₂` from the nibble `v`: its bits 2 and 3. -/
def cbdY (v : Nat) : Nat := v / 4 % 2 + v / 8 % 2

/-- Nibble `i` of `B` (the low nibble of byte `⌊i/2⌋` for even `i`, the high
one for odd `i`), shifted down: its low 4 bits are the nibble. -/
def nibble (B : List Byte) (i : Nat) : Nat := (B.getD (i / 2) 0).toNat / 16 ^ (i % 2)

private theorem cbd_bit (B : List Byte) (i j : Nat) (hj : j < 4) :
    ((bytesToBits B).getD (2 * i * 2 + j) false).toNat = nibble B i / 2 ^ j % 2 := by
  rw [bytesToBits_getD, nibble, show (2 * i * 2 + j) / 8 = i / 2 by omega,
    show (2 * i * 2 + j) % 8 = 4 * (i % 2) + j by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul,
    Nat.pow_mul]

/-- Coefficient `i` of `SamplePolyCBD₂(B)`: `x - y` for the bits `x` and `y`
of nibble `i`. -/
theorem samplePolyCBD2_get (B : List Byte) {i : Nat} (hi : i < n) :
    (samplePolyCBD 2 B)[i]! = ofNat (cbdX (nibble B i)) - ofNat (cbdY (nibble B i)) := by
  rw [getElem!_eq _ hi]
  simp only [samplePolyCBD, Vector.getElem_ofFn, range2, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]
  have h0 := cbd_bit B i 0 (by decide)
  rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
  rw [h0, cbd_bit B i 1 (by decide), show 2 * i * 2 + 2 + 1 = 2 * i * 2 + 3 by omega,
    cbd_bit B i 2 (by decide), cbd_bit B i 3 (by decide)]
  simp only [cbdX, cbdY, Nat.reducePow]

theorem cbdX_le (v : Nat) : cbdX v ≤ 2 := by unfold cbdX; omega

theorem cbdY_le (v : Nat) : cbdY v ≤ 2 := by unfold cbdY; omega

/-- Coefficient `i` of `SamplePolyCBD₂(B)`, as an integer: `x + q - y`,
reduced. -/
theorem samplePolyCBD2_val (B : List Byte) {i : Nat} (hi : i < n) :
    ((samplePolyCBD 2 B)[i]!).val = (cbdX (nibble B i) + q - cbdY (nibble B i)) % q := by
  have := cbdX_le (nibble B i); have := cbdY_le (nibble B i)
  rw [samplePolyCBD2_get B hi, val_sub', ofNat_of_lt (by rw [q_eq]; omega),
    ofNat_of_lt (by rw [q_eq]; omega), Nat.add_sub_assoc (by rw [q_eq]; omega)]

end VG.Proof.MlKem
