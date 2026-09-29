import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming SHA-512: facts about the specification

Untrusted: everything here is checked by Lean. How `Repr` evolves as bytes
are buffered and blocks compressed, and how the padded message decomposes,
independently of any target.
-/

namespace VG.Proof.Sha512.Stream

open VG.Spec.Sha512

/-- Block `i` of the bytes `p`. -/
def blockOf (p : List Byte) (i : Nat) : Block := parseBlock fun k => p.getD (128 * i + k) 0

theorem compressList_succ (H : HashValue) (p : List Byte) (n : Nat) :
    compressList H p (n + 1) = compress (compressList H p n) (blockOf p n) := by
  simp only [compressList, List.range_succ, List.foldl_append, blockOf, List.foldl_cons, List.foldl_nil]

theorem compressList_zero (H : HashValue) (p : List Byte) : compressList H p 0 = H := by
  simp only [compressList, List.range_zero, List.foldl_nil]

theorem compressList_congr {H : HashValue} {p q : List Byte} {n : Nat}
    (h : ∀ j < 128 * n, p.getD j 0 = q.getD j 0) : compressList H p n = compressList H q n := by
  induction n with
  | zero => simp only [compressList_zero]
  | succ n ih =>
    rw [compressList_succ, compressList_succ, ih fun j hj => h j (by omega)]
    have : blockOf p n = blockOf q n := by
      funext t
      simp only [blockOf, parseBlock]
      have ht := t.isLt
      rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega),
        h _ (by omega), h _ (by omega), h _ (by omega)]
    rw [this]

theorem compressList_add (H : HashValue) (p : List Byte) (a b : Nat) :
    compressList H p (a + b) = compressList (compressList H p a) (p.drop (128 * a)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, compressList_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, compressList_succ, compressList_succ, ih]
    have : blockOf p (a + b) = blockOf (p.drop (128 * a)) b := by
      funext t
      simp only [blockOf, parseBlock, List.getD_eq_getElem?_getD, List.getElem?_drop]
      simp only [Nat.mul_add, Nat.add_assoc]
    rw [this]

theorem getD_append_left {p q : List Byte} {j : Nat} (h : j < p.length) :
    (p ++ q).getD j 0 = p.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem compressList_append {H : HashValue} {p q : List Byte} {n : Nat} (h : 128 * n ≤ p.length) :
    compressList H (p ++ q) n = compressList H p n :=
  compressList_congr fun _ hj => getD_append_left (by omega)

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr} (h : ∀ i < 64, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    stateAt mem' p = stateAt mem p := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  apply Mem.readW_congr
  intro i hi
  rw [show p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (8 * k + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]]
  exact h _ (by omega)

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    bytesAt mem' p n = bytesAt mem p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- `Repr` only depends on the 192 bytes of the state. -/
theorem repr_congr {iv : HashValue} {mem mem' : Mem} {p : Addr} {m : List Byte}
    (h : ∀ i < 192, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha512.Repr iv mem p m) : Spec.Sha512.Repr iv mem' p m := by
  refine ⟨by rw [stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply bytesAt_congr
  intro i hi
  have := h (64 + i) (by omega)
  rwa [show p + 64 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (64 + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]

export VG.WriteBytes (writeBytes writeBytes_nil writeW8_apply writeBytes_snoc writeBytes_before writeBytes_frame write_eq_writeBytes writeBytes_append)

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) = bytesAt m p r ++ xs := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    exact writeBytes_before m p xs hi (by omega)
  · apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Function.comp, writeBytes]
    have hj : j < xs.length := by simpa using h₁
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j from
      Offset.add_ofNat_add_sub p r j, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

/-! ## `Repr` -/

theorem repr_nil {iv : HashValue} {mem : Mem} {p : Addr} (h : stateAt mem p = iv) : Spec.Sha512.Repr iv mem p [] := by
  simp [Spec.Sha512.Repr, h, compressList_zero, bytesAt]

/-- Appending bytes that stay within the buffer. -/
theorem repr_append_buf {iv : HashValue} {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha512.Repr iv mem p m)
    (hlen : m.length % 128 + xs.length < 128) (hs : stateAt mem' p = stateAt mem p)
    (hb : bytesAt mem' (p + 64) (m.length % 128 + xs.length) = m.drop (128 * (m.length / 128)) ++ xs) :
    Spec.Sha512.Repr iv mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 128 = m.length / 128 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 128 = m.length % 128 + xs.length := by
    simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · rw [hs, hr.1, hdiv, compressList_append (by omega)]
  · rw [hmod, hb, hdiv, List.drop_append_of_le_length (by omega)]

/-- Appending bytes that complete a block `B` (whose bytes are the buffered
ones followed by `xs`), which is compressed. -/
theorem repr_append_block {iv : HashValue} {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha512.Repr iv mem p m)
    (hlen : m.length % 128 + xs.length = 128)
    (hs : stateAt mem' p =
      compress (stateAt mem p) (parseBlock fun k => (m.drop (128 * (m.length / 128)) ++ xs).getD k 0)) :
    Spec.Sha512.Repr iv mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 128 = m.length / 128 + 1 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 128 = 0 := by simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · have hb : blockOf (m ++ xs) (m.length / 128) =
        parseBlock fun k => (m.drop (128 * (m.length / 128)) ++ xs).getD k 0 := by
      rw [← List.drop_append_of_le_length (by omega)]
      simp only [blockOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hs, hr.1, hdiv, compressList_succ, compressList_append (by omega), hb]
  · rw [hmod]
    simp only [bytesAt, List.range_zero, List.map_nil]
    symm; rw [List.drop_eq_nil_iff]; simp only [List.length_append]; omega

/-! ## Padding -/

/-- The message length in bits, as 16 big-endian bytes. -/
def lenBytes (m : List Byte) : List Byte :=
  (List.range 16).reverse.map fun i => (BitVec.ofNat 128 (8 * m.length)).extractLsb' (8 * i) 8

theorem lenBytes_length (m : List Byte) : (lenBytes m).length = 16 := by simp [lenBytes]

/-- For fewer than 2⁶⁴ bytes, the 128-bit length in bits is the 64-bit words
`n >> 61` and `8 n mod 2⁶⁴`, big-endian. -/
theorem lenN_split (n : Nat) (h : n < 2 ^ 64) :
    (List.range 16).reverse.map (fun i => (BitVec.ofNat 128 (8 * n)).extractLsb' (8 * i) 8) =
      wordBytes (BitVec.ofNat 64 n >>> 61) ++ wordBytes (BitVec.ofNat 64 (8 * n)) := by
  have key : BitVec.ofNat 128 (8 * n) = (BitVec.ofNat 64 n >>> 61) ++ BitVec.ofNat 64 (8 * n) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), Nat.shiftLeft_eq]
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  rw [key]
  generalize BitVec.ofNat 64 n >>> 61 = x
  generalize BitVec.ofNat 64 (8 * n) = y
  simp only [wordBytes, List.range_succ, List.range_zero, List.nil_append,
    List.reverse_cons, List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  simp (disch := decide) only [BitVec.extractLsb'_append_eq_of_add_le,
    BitVec.extractLsb'_append_eq_of_le]

/-- For a message of fewer than 2⁶⁴ bytes, the 128-bit length in bits is the
64-bit words `|m| >> 61` and `8 |m| mod 2⁶⁴`, big-endian. -/
theorem lenBytes_split (m : List Byte) (h : m.length < 2 ^ 64) :
    lenBytes m = wordBytes (BitVec.ofNat 64 m.length >>> 61) ++ wordBytes (BitVec.ofNat 64 (8 * m.length)) :=
  lenN_split m.length h

/-- The bytes after the whole blocks of `m`. -/
abbrev rest (m : List Byte) : List Byte := m.drop (128 * (m.length / 128))

theorem rest_length (m : List Byte) : (rest m).length = m.length % 128 := by
  simp only [rest, List.length_drop]; omega

theorem compressList_one (H : HashValue) (p : List Byte) :
    compressList H p 1 = compress H (parseBlock fun t => p.getD t 0) := by
  rw [compressList_succ, compressList_zero]; simp [blockOf]

theorem hash_eq (iv : HashValue) (m : List Byte) (nt : Nat)
    (hn : (m.length % 128 + 1 + (239 - m.length % 128) % 128 + 16) = 128 * nt) :
    Spec.Sha512.finalHash iv m = (compressList (compressList iv m (m.length / 128))
      (rest m ++ [0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++ lenBytes m) nt).toList.flatMap
        wordBytes := by
  have hp : pad m = m ++ ([0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++ lenBytes m) := by
    simp [pad, lenBytes, List.append_assoc]
  have hlen : (pad m).length / 128 = m.length / 128 + nt := by
    rw [hp]; simp only [List.length_append, List.length_replicate, lenBytes_length, List.length_singleton]
    omega
  simp only [Spec.Sha512.finalHash]
  rw [hlen, compressList_add, hp, compressList_append (by omega),
    List.drop_append_of_le_length (by omega)]
  simp only [List.append_assoc]

theorem parseBlock_congr {f g : Nat → Byte} (h : ∀ k < 128, f k = g k) : parseBlock f = parseBlock g := by
  funext j
  have := j.isLt
  simp only [parseBlock]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega),
    h _ (by omega), h _ (by omega), h _ (by omega)]

/-- A message whose padding takes one more block. -/
theorem hash_one {iv : HashValue} {m : List Byte} (hr : m.length % 128 < 112) :
    Spec.Sha512.finalHash iv m = (compress (compressList iv m (m.length / 128))
      (parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (111 - m.length % 128) 0 ++
        lenBytes m).getD t 0)).toList.flatMap wordBytes := by
  rw [hash_eq iv m 1 (by omega), compressList_one,
    show (239 - m.length % 128) % 128 = 111 - m.length % 128 by omega]

theorem getD_append_right {p q : List Byte} {j : Nat} :
    (p ++ q).getD (p.length + j) 0 = q.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- A message whose padding takes two more blocks. -/
theorem hash_two {iv : HashValue} {m : List Byte} (hr : 112 ≤ m.length % 128) :
    Spec.Sha512.finalHash iv m = (compress (compress (compressList iv m (m.length / 128))
      (parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0).getD t 0))
      (parseBlock fun t => (List.replicate 112 0 ++ lenBytes m).getD t 0)).toList.flatMap wordBytes := by
  rw [hash_eq iv m 2 (by omega), compressList_succ, compressList_one]
  have e : rest m ++ [0x80] ++ List.replicate ((239 - m.length % 128) % 128) 0 ++ lenBytes m =
      (rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0) ++
        (List.replicate 112 0 ++ lenBytes m) := by
    rw [show (239 - m.length % 128) % 128 = (127 - m.length % 128) + 112 by omega, ← List.replicate_append_replicate]
    simp only [List.append_assoc]
  have hl : (rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0).length = 128 := by
    simp only [List.length_append, rest_length, List.length_replicate, List.length_singleton]; omega
  rw [e]
  have h1 : (parseBlock fun t => ((rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0) ++
      (List.replicate 112 0 ++ lenBytes m)).getD t 0) =
      parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0).getD t 0 :=
    parseBlock_congr fun k hk => getD_append_left (by omega)
  have h2 : blockOf ((rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0) ++
      (List.replicate 112 0 ++ lenBytes m)) 1 =
      parseBlock fun t => (List.replicate 112 0 ++ lenBytes m).getD t 0 :=
    parseBlock_congr fun k _ => by
      have := getD_append_right (p := rest m ++ [0x80] ++ List.replicate (127 - m.length % 128) 0)
        (q := List.replicate 112 0 ++ lenBytes m) (j := k)
      rw [hl] at this
      exact this
  rw [h1, h2]

end VG.Proof.Sha512.Stream
