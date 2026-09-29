import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.MlKem.Compress1024

/-!
# ML-KEM-1024: compressed encodings byte by byte, for every target

Untrusted: everything here is checked by Lean. The analog of the compressed
encodings of `Encode.lean` for the widths only ML-KEM-1024 compresses to,
group by group as the arithmetic an implementation does (with `Bits.lean`):

* `ByteEncode₅ ∘ Compress₅`: 8 coefficients per 5 bytes
  (`compressEncode5_group`, the 40-bit number of the group, and
  `compressEncode5_0` … `_4`, byte by byte), and `Decompress₅ ∘ ByteDecode₅`
  (`decodeDecompress5_group` and `decodeDecompress5_0` … `_7`, field by
  field);
* `ByteEncode₁₁ ∘ Compress₁₁`: 8 coefficients per 11 bytes
  (`compressEncode11_group`, `compressEncode11_0` … `_10`), and
  `Decompress₁₁ ∘ ByteDecode₁₁` (`decodeDecompress11_group`,
  `decodeDecompress11_0` … `_7`).

Byte `k` of a list `B` is written `B.getD k 0`, which `bytesAt_getD`
(`Mem.lean`) reads from memory, and byte `k` of an encoding `L[k]!`, which
`bytesAt_eq!` takes.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

theorem range11 : List.range 11 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] := rfl

/-! ## ByteEncode₅ ∘ Compress₅ -/

/-- Byte `5g + j` of `ByteEncode₅(Compress₅(f))`: byte `j` of the 40-bit
number of the compressed coefficients `8g … 8g + 7`. -/
theorem compressEncode5_group (f : Poly) {g j : Nat} (hg : g < 32) (hj : j < 5) :
    (compressEncode 5 f)[5 * g + j]! = BitVec.ofNat 8 ((compress 5 f[8 * g]! +
      32 * compress 5 f[8 * g + 1]! + 1024 * compress 5 f[8 * g + 2]! +
      32768 * compress 5 f[8 * g + 3]! + 1048576 * compress 5 f[8 * g + 4]! +
      33554432 * compress 5 f[8 * g + 5]! + 1073741824 * compress 5 f[8 * g + 6]! +
      34359738368 * compress 5 f[8 * g + 7]!) / 2 ^ (8 * j)) := by
  rw [compressEncode, byteEncode_group (c := 8) (by decide) (by decide)
    (map_toList_lt f (compress_lt 5)) hj (by omega), take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  simp only [range8, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  simp (disch := omega) only [map_toList_getD]
  refine congrArg (BitVec.ofNat 8) (congrArg (· / 2 ^ (8 * j)) ?_)
  omega

section
variable (f : Poly) {g : Nat} (hg : g < 32)
include hg

omit hg in
private theorem c5_lt (i : Nat) : compress 5 f[i]! < 32 := compress_lt 5 _

omit hg in
private theorem c5_lts (g : Nat) : compress 5 f[8 * g]! < 32 ∧ compress 5 f[8 * g + 1]! < 32 ∧
    compress 5 f[8 * g + 2]! < 32 ∧ compress 5 f[8 * g + 3]! < 32 ∧
    compress 5 f[8 * g + 4]! < 32 ∧ compress 5 f[8 * g + 5]! < 32 ∧
    compress 5 f[8 * g + 6]! < 32 ∧ compress 5 f[8 * g + 7]! < 32 :=
  ⟨c5_lt f _, c5_lt f _, c5_lt f _, c5_lt f _, c5_lt f _, c5_lt f _, c5_lt f _, c5_lt f _⟩

theorem compressEncode5_0 :
    (compressEncode 5 f)[5 * g]! =
      BitVec.ofNat 8 (compress 5 f[8 * g]! + 32 * (compress 5 f[8 * g + 1]! % 8)) := by
  have h := compressEncode5_group f hg (j := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  have := c5_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode5_1 :
    (compressEncode 5 f)[5 * g + 1]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 1]! / 8 + 4 * compress 5 f[8 * g + 2]! +
        128 * (compress 5 f[8 * g + 3]! % 2)) := by
  rw [compressEncode5_group f hg (by decide)]
  have := c5_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode5_2 :
    (compressEncode 5 f)[5 * g + 2]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 3]! / 2 + 16 * (compress 5 f[8 * g + 4]! % 16)) := by
  rw [compressEncode5_group f hg (by decide)]
  have := c5_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode5_3 :
    (compressEncode 5 f)[5 * g + 3]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 4]! / 16 + 2 * compress 5 f[8 * g + 5]! +
        64 * (compress 5 f[8 * g + 6]! % 4)) := by
  rw [compressEncode5_group f hg (by decide)]
  have := c5_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode5_4 :
    (compressEncode 5 f)[5 * g + 4]! =
      BitVec.ofNat 8 (compress 5 f[8 * g + 6]! / 4 + 8 * compress 5 f[8 * g + 7]!) := by
  rw [compressEncode5_group f hg (by decide)]
  have := c5_lts f g
  exact ofNat8_eq (by omega)

end

/-! ## ByteEncode₁₁ ∘ Compress₁₁ -/

/-- Byte `11g + j` of `ByteEncode₁₁(Compress₁₁(f))`: byte `j` of the 88-bit
number of the compressed coefficients `8g … 8g + 7`. -/
theorem compressEncode11_group (f : Poly) {g j : Nat} (hg : g < 32) (hj : j < 11) :
    (compressEncode 11 f)[11 * g + j]! = BitVec.ofNat 8 ((compress 11 f[8 * g]! +
      2048 * compress 11 f[8 * g + 1]! + 4194304 * compress 11 f[8 * g + 2]! +
      8589934592 * compress 11 f[8 * g + 3]! + 17592186044416 * compress 11 f[8 * g + 4]! +
      36028797018963968 * compress 11 f[8 * g + 5]! +
      73786976294838206464 * compress 11 f[8 * g + 6]! +
      151115727451828646838272 * compress 11 f[8 * g + 7]!) / 2 ^ (8 * j)) := by
  rw [compressEncode, byteEncode_group (c := 8) (by decide) (by decide)
    (map_toList_lt f (compress_lt 11)) hj (by omega), take_drop_eq _ 0 (by rw [map_toList_length]; omega)]
  simp only [range8, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero]
  simp (disch := omega) only [map_toList_getD]
  refine congrArg (BitVec.ofNat 8) (congrArg (· / 2 ^ (8 * j)) ?_)
  omega

section
variable (f : Poly) {g : Nat} (hg : g < 32)
include hg

omit hg in
private theorem c11_lt (i : Nat) : compress 11 f[i]! < 2048 := compress_lt 11 _

omit hg in
private theorem c11_lts (g : Nat) : compress 11 f[8 * g]! < 2048 ∧ compress 11 f[8 * g + 1]! < 2048 ∧
    compress 11 f[8 * g + 2]! < 2048 ∧ compress 11 f[8 * g + 3]! < 2048 ∧
    compress 11 f[8 * g + 4]! < 2048 ∧ compress 11 f[8 * g + 5]! < 2048 ∧
    compress 11 f[8 * g + 6]! < 2048 ∧ compress 11 f[8 * g + 7]! < 2048 :=
  ⟨c11_lt f _, c11_lt f _, c11_lt f _, c11_lt f _, c11_lt f _, c11_lt f _, c11_lt f _, c11_lt f _⟩

theorem compressEncode11_0 :
    (compressEncode 11 f)[11 * g]! = BitVec.ofNat 8 (compress 11 f[8 * g]! % 256) := by
  have h := compressEncode11_group f hg (j := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_1 :
    (compressEncode 11 f)[11 * g + 1]! =
      BitVec.ofNat 8 (compress 11 f[8 * g]! / 256 + 8 * (compress 11 f[8 * g + 1]! % 32)) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_2 :
    (compressEncode 11 f)[11 * g + 2]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 1]! / 32 + 64 * (compress 11 f[8 * g + 2]! % 4)) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_3 :
    (compressEncode 11 f)[11 * g + 3]! = BitVec.ofNat 8 (compress 11 f[8 * g + 2]! / 4 % 256) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_4 :
    (compressEncode 11 f)[11 * g + 4]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 2]! / 1024 + 2 * (compress 11 f[8 * g + 3]! % 128)) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_5 :
    (compressEncode 11 f)[11 * g + 5]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 3]! / 128 + 16 * (compress 11 f[8 * g + 4]! % 16)) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_6 :
    (compressEncode 11 f)[11 * g + 6]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 4]! / 16 + 128 * (compress 11 f[8 * g + 5]! % 2)) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_7 :
    (compressEncode 11 f)[11 * g + 7]! = BitVec.ofNat 8 (compress 11 f[8 * g + 5]! / 2 % 256) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_8 :
    (compressEncode 11 f)[11 * g + 8]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 5]! / 512 + 4 * (compress 11 f[8 * g + 6]! % 64)) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_9 :
    (compressEncode 11 f)[11 * g + 9]! =
      BitVec.ofNat 8 (compress 11 f[8 * g + 6]! / 64 + 32 * (compress 11 f[8 * g + 7]! % 8)) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

theorem compressEncode11_10 :
    (compressEncode 11 f)[11 * g + 10]! = BitVec.ofNat 8 (compress 11 f[8 * g + 7]! / 8) := by
  rw [compressEncode11_group f hg (by decide)]
  have := c11_lts f g
  exact ofNat8_eq (by omega)

end

/-! ## Decompress₅ ∘ ByteDecode₅ -/

/-- Coefficient `8g + e` of `Decompress₅(ByteDecode₅(B))`: 5-bit field `e`
of the 40-bit number of bytes `5g … 5g + 4`. -/
theorem decodeDecompress5_group (B : List Byte) (hB : B.length = 160) {g e : Nat}
    (hg : g < 32) (he : e < 8) :
    (decodeDecompress 5 B)[8 * g + e]! = decompress 5 (((B.getD (5 * g) 0).toNat +
      256 * (B.getD (5 * g + 1) 0).toNat + 65536 * (B.getD (5 * g + 2) 0).toNat +
      16777216 * (B.getD (5 * g + 3) 0).toNat + 4294967296 * (B.getD (5 * g + 4) 0).toNat) /
        2 ^ (5 * e) % 32) := by
  rw [decodeDecompress_get 5 B (by rw [n_eq]; omega), byteDecode_group (c := 8) (b := 5) (by decide) B
    he (by rw [n_eq]; omega), bytes_map_take_drop B (by omega)]
  simp only [range5, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.reduceLT, ↓reduceIte, Nat.mod_mod]
  refine congrArg (decompress 5) (congrArg (· % 32) (congrArg (· / 2 ^ (5 * e)) ?_))
  omega

section
variable (B : List Byte) (hB : B.length = 160) {g : Nat} (hg : g < 32)
include hB hg

omit hB hg in
private theorem bytes5_lt' : (B.getD (5 * g) 0).toNat < 256 ∧ (B.getD (5 * g + 1) 0).toNat < 256 ∧
    (B.getD (5 * g + 2) 0).toNat < 256 ∧ (B.getD (5 * g + 3) 0).toNat < 256 ∧
    (B.getD (5 * g + 4) 0).toNat < 256 :=
  ⟨byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _⟩

theorem decodeDecompress5_0 :
    (decodeDecompress 5 B)[8 * g]! = decompress 5 ((B.getD (5 * g) 0).toNat % 32) := by
  have h := decodeDecompress5_group B hB hg (e := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

theorem decodeDecompress5_1 :
    (decodeDecompress 5 B)[8 * g + 1]! = decompress 5 ((B.getD (5 * g) 0).toNat / 32 +
      8 * ((B.getD (5 * g + 1) 0).toNat % 4)) := by
  rw [decodeDecompress5_group B hB hg (by decide)]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

theorem decodeDecompress5_2 :
    (decodeDecompress 5 B)[8 * g + 2]! = decompress 5 ((B.getD (5 * g + 1) 0).toNat / 4 % 32) := by
  rw [decodeDecompress5_group B hB hg (by decide)]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

theorem decodeDecompress5_3 :
    (decodeDecompress 5 B)[8 * g + 3]! = decompress 5 ((B.getD (5 * g + 1) 0).toNat / 128 +
      2 * ((B.getD (5 * g + 2) 0).toNat % 16)) := by
  rw [decodeDecompress5_group B hB hg (by decide)]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

theorem decodeDecompress5_4 :
    (decodeDecompress 5 B)[8 * g + 4]! = decompress 5 ((B.getD (5 * g + 2) 0).toNat / 16 +
      16 * ((B.getD (5 * g + 3) 0).toNat % 2)) := by
  rw [decodeDecompress5_group B hB hg (by decide)]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

theorem decodeDecompress5_5 :
    (decodeDecompress 5 B)[8 * g + 5]! = decompress 5 ((B.getD (5 * g + 3) 0).toNat / 2 % 32) := by
  rw [decodeDecompress5_group B hB hg (by decide)]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

theorem decodeDecompress5_6 :
    (decodeDecompress 5 B)[8 * g + 6]! = decompress 5 ((B.getD (5 * g + 3) 0).toNat / 64 +
      4 * ((B.getD (5 * g + 4) 0).toNat % 8)) := by
  rw [decodeDecompress5_group B hB hg (by decide)]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

theorem decodeDecompress5_7 :
    (decodeDecompress 5 B)[8 * g + 7]! = decompress 5 ((B.getD (5 * g + 4) 0).toNat / 8) := by
  rw [decodeDecompress5_group B hB hg (by decide)]
  refine congrArg (decompress 5) ?_
  have := bytes5_lt' B (g := g)
  omega

end

/-! ## Decompress₁₁ ∘ ByteDecode₁₁ -/

/-- The number whose base-256 digits are 11 bytes. -/
private theorem bytes11_eq (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat) :
    b0 + 2 ^ 8 * (b1 + 2 ^ 8 * (b2 + 2 ^ 8 * (b3 + 2 ^ 8 * (b4 + 2 ^ 8 * (b5 + 2 ^ 8 * (b6 +
      2 ^ 8 * (b7 + 2 ^ 8 * (b8 + 2 ^ 8 * (b9 + 2 ^ 8 * (b10 + 2 ^ 8 * 0)))))))))) =
    b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4 + 1099511627776 * b5 +
      281474976710656 * b6 + 72057594037927936 * b7 + 18446744073709551616 * b8 +
      4722366482869645213696 * b9 + 1208925819614629174706176 * b10 := by
  omega

/-- Coefficient `8g + e` of `Decompress₁₁(ByteDecode₁₁(B))`: 11-bit field
`e` of the 88-bit number of bytes `11g … 11g + 10`. -/
theorem decodeDecompress11_group (B : List Byte) (hB : B.length = 352) {g e : Nat}
    (hg : g < 32) (he : e < 8) :
    (decodeDecompress 11 B)[8 * g + e]! = decompress 11 (((B.getD (11 * g) 0).toNat +
      256 * (B.getD (11 * g + 1) 0).toNat + 65536 * (B.getD (11 * g + 2) 0).toNat +
      16777216 * (B.getD (11 * g + 3) 0).toNat + 4294967296 * (B.getD (11 * g + 4) 0).toNat +
      1099511627776 * (B.getD (11 * g + 5) 0).toNat +
      281474976710656 * (B.getD (11 * g + 6) 0).toNat +
      72057594037927936 * (B.getD (11 * g + 7) 0).toNat +
      18446744073709551616 * (B.getD (11 * g + 8) 0).toNat +
      4722366482869645213696 * (B.getD (11 * g + 9) 0).toNat +
      1208925819614629174706176 * (B.getD (11 * g + 10) 0).toNat) / 2 ^ (11 * e) % 2048) := by
  rw [decodeDecompress_get 11 B (by rw [n_eq]; omega), byteDecode_group (c := 8) (b := 11) (by decide)
    B he (by rw [n_eq]; omega), bytes_map_take_drop B (by omega)]
  simp only [range11, List.map_cons, List.map_nil, digits_cons, digits_nil, Nat.add_zero,
    Nat.reduceLT, ↓reduceIte, Nat.mod_mod]
  exact congrArg (decompress 11) (congrArg (· % 2048) (congrArg (· / 2 ^ (11 * e)) (bytes11_eq ..)))

section
variable (B : List Byte) (hB : B.length = 352) {g : Nat} (hg : g < 32)
include hB hg

omit hB hg in
private theorem bytes11_lt : (B.getD (11 * g) 0).toNat < 256 ∧ (B.getD (11 * g + 1) 0).toNat < 256 ∧
    (B.getD (11 * g + 2) 0).toNat < 256 ∧ (B.getD (11 * g + 3) 0).toNat < 256 ∧
    (B.getD (11 * g + 4) 0).toNat < 256 ∧ (B.getD (11 * g + 5) 0).toNat < 256 ∧
    (B.getD (11 * g + 6) 0).toNat < 256 ∧ (B.getD (11 * g + 7) 0).toNat < 256 ∧
    (B.getD (11 * g + 8) 0).toNat < 256 ∧ (B.getD (11 * g + 9) 0).toNat < 256 ∧
    (B.getD (11 * g + 10) 0).toNat < 256 :=
  ⟨byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _, byte_lt _,
    byte_lt _, byte_lt _, byte_lt _⟩

theorem decodeDecompress11_0 :
    (decodeDecompress 11 B)[8 * g]! = decompress 11 ((B.getD (11 * g) 0).toNat +
      256 * ((B.getD (11 * g + 1) 0).toNat % 8)) := by
  have h := decodeDecompress11_group B hB hg (e := 0) (by decide)
  rw [Nat.add_zero] at h
  rw [h]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

theorem decodeDecompress11_1 :
    (decodeDecompress 11 B)[8 * g + 1]! = decompress 11 ((B.getD (11 * g + 1) 0).toNat / 8 +
      32 * ((B.getD (11 * g + 2) 0).toNat % 64)) := by
  rw [decodeDecompress11_group B hB hg (by decide)]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

theorem decodeDecompress11_2 :
    (decodeDecompress 11 B)[8 * g + 2]! = decompress 11 ((B.getD (11 * g + 2) 0).toNat / 64 +
      4 * (B.getD (11 * g + 3) 0).toNat + 1024 * ((B.getD (11 * g + 4) 0).toNat % 2)) := by
  rw [decodeDecompress11_group B hB hg (by decide)]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

theorem decodeDecompress11_3 :
    (decodeDecompress 11 B)[8 * g + 3]! = decompress 11 ((B.getD (11 * g + 4) 0).toNat / 2 +
      128 * ((B.getD (11 * g + 5) 0).toNat % 16)) := by
  rw [decodeDecompress11_group B hB hg (by decide)]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

theorem decodeDecompress11_4 :
    (decodeDecompress 11 B)[8 * g + 4]! = decompress 11 ((B.getD (11 * g + 5) 0).toNat / 16 +
      16 * ((B.getD (11 * g + 6) 0).toNat % 128)) := by
  rw [decodeDecompress11_group B hB hg (by decide)]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

theorem decodeDecompress11_5 :
    (decodeDecompress 11 B)[8 * g + 5]! = decompress 11 ((B.getD (11 * g + 6) 0).toNat / 128 +
      2 * (B.getD (11 * g + 7) 0).toNat + 512 * ((B.getD (11 * g + 8) 0).toNat % 4)) := by
  rw [decodeDecompress11_group B hB hg (by decide)]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

theorem decodeDecompress11_6 :
    (decodeDecompress 11 B)[8 * g + 6]! = decompress 11 ((B.getD (11 * g + 8) 0).toNat / 4 +
      64 * ((B.getD (11 * g + 9) 0).toNat % 32)) := by
  rw [decodeDecompress11_group B hB hg (by decide)]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

theorem decodeDecompress11_7 :
    (decodeDecompress 11 B)[8 * g + 7]! = decompress 11 ((B.getD (11 * g + 9) 0).toNat / 32 +
      8 * (B.getD (11 * g + 10) 0).toNat) := by
  rw [decodeDecompress11_group B hB hg (by decide)]
  refine congrArg (decompress 11) ?_
  have := bytes11_lt B (g := g)
  omega

end

end VG.Proof.MlKem
