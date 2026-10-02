import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming MD5: facts about the specification

How `Repr` evolves as bytes are buffered and blocks compressed, and how the
padded message decomposes, independently of any target.
-/

namespace VG.Proof.Md5.Stream

open VG.Spec.Md5

/-- Block `i` of the bytes `p`. -/
def blockOf (p : List Byte) (i : Nat) : Block := parseBlock fun k => p.getD (64 * i + k) 0

theorem compressList_succ (H : HashValue) (p : List Byte) (n : Nat) :
    compressList H p (n + 1) = compress (compressList H p n) (blockOf p n) := by
  simp only [compressList, List.range_succ, List.foldl_append, blockOf, List.foldl_cons, List.foldl_nil]

theorem compressList_zero (H : HashValue) (p : List Byte) : compressList H p 0 = H := by
  simp only [compressList, List.range_zero, List.foldl_nil]

theorem compressList_congr {H : HashValue} {p q : List Byte} {n : Nat}
    (h : ∀ j < 64 * n, p.getD j 0 = q.getD j 0) : compressList H p n = compressList H q n := by
  induction n with
  | zero => simp only [compressList_zero]
  | succ n ih =>
    rw [compressList_succ, compressList_succ, ih fun j hj => h j (by omega)]
    have : blockOf p n = blockOf q n := by
      funext t
      simp only [blockOf, parseBlock]
      have ht := t.isLt
      rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]
    rw [this]

theorem compressList_add (H : HashValue) (p : List Byte) (a b : Nat) :
    compressList H p (a + b) = compressList (compressList H p a) (p.drop (64 * a)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, compressList_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, compressList_succ, compressList_succ, ih]
    have : blockOf p (a + b) = blockOf (p.drop (64 * a)) b := by
      funext t
      simp only [blockOf, parseBlock, List.getD_eq_getElem?_getD, List.getElem?_drop]
      simp only [Nat.mul_add, Nat.add_assoc]
    rw [this]

theorem getD_append_left {p q : List Byte} {j : Nat} (h : j < p.length) :
    (p ++ q).getD j 0 = p.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem compressList_append {H : HashValue} {p q : List Byte} {n : Nat} (h : 64 * n ≤ p.length) :
    compressList H (p ++ q) n = compressList H p n :=
  compressList_congr fun _ hj => getD_append_left (by omega)

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr} (h : ∀ i < 16, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    stateAt mem' p = stateAt mem p := by
  apply Vector.ext
  intro k hk
  simp only [stateAt, Vector.getElem_ofFn]
  apply Mem.readW_congr
  intro i hi
  rw [show p + BitVec.ofNat 64 (4 * k) + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (4 * k + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]]
  exact h _ (by omega)

theorem bytesAt_congr {mem mem' : Mem} {p : Addr} {n : Nat}
    (h : ∀ i < n, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
    bytesAt mem' p n = bytesAt mem p n := by
  simp only [bytesAt]
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)

/-- `Repr` only depends on the 80 bytes of the state. -/
theorem repr_congr {mem mem' : Mem} {p : Addr} {m : List Byte}
    (h : ∀ i < 80, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Spec.Md5.Repr mem p m) : Spec.Md5.Repr mem' p m := by
  refine ⟨by rw [stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply bytesAt_congr
  intro i hi
  have := h (16 + i) (by omega)
  rwa [show p + 16 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (16 + i) by
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

theorem repr_nil {mem : Mem} {p : Addr} (h : stateAt mem p = H0) : Spec.Md5.Repr mem p [] := by
  simp [Spec.Md5.Repr, h, compressList_zero, bytesAt]

/-- Appending bytes that stay within the buffer. -/
theorem repr_append_buf {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Md5.Repr mem p m)
    (hlen : m.length % 64 + xs.length < 64) (hs : stateAt mem' p = stateAt mem p)
    (hb : bytesAt mem' (p + 16) (m.length % 64 + xs.length) = m.drop (64 * (m.length / 64)) ++ xs) :
    Spec.Md5.Repr mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 64 = m.length / 64 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 64 = m.length % 64 + xs.length := by
    simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · rw [hs, hr.1, hdiv, compressList_append (by omega)]
  · rw [hmod, hb, hdiv, List.drop_append_of_le_length (by omega)]

/-- Appending bytes that complete a block `B` (whose bytes are the buffered
ones followed by `xs`), which is compressed. -/
theorem repr_append_block {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Md5.Repr mem p m)
    (hlen : m.length % 64 + xs.length = 64)
    (hs : stateAt mem' p =
      compress (stateAt mem p) (parseBlock fun k => (m.drop (64 * (m.length / 64)) ++ xs).getD k 0)) :
    Spec.Md5.Repr mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 64 = m.length / 64 + 1 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 64 = 0 := by simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · have hb : blockOf (m ++ xs) (m.length / 64) =
        parseBlock fun k => (m.drop (64 * (m.length / 64)) ++ xs).getD k 0 := by
      rw [← List.drop_append_of_le_length (by omega)]
      simp only [blockOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hs, hr.1, hdiv, compressList_succ, compressList_append (by omega), hb]
  · rw [hmod]
    simp only [bytesAt, List.range_zero, List.map_nil]
    symm; rw [List.drop_eq_nil_iff]; simp only [List.length_append]; omega

/-! ## Padding -/

/-- The message length in bits (modulo 2⁶⁴), as 8 little-endian bytes. -/
def lenBytes (m : List Byte) : List Byte :=
  (List.range 8).map fun i => (BitVec.ofNat 64 (8 * m.length)).extractLsb' (8 * i) 8

theorem lenBytes_length (m : List Byte) : (lenBytes m).length = 8 := by simp [lenBytes]

/-- The bytes after the whole blocks of `m`. -/
abbrev rest (m : List Byte) : List Byte := m.drop (64 * (m.length / 64))

theorem rest_length (m : List Byte) : (rest m).length = m.length % 64 := by
  simp only [rest, List.length_drop]; omega

theorem compressList_one (H : HashValue) (p : List Byte) :
    compressList H p 1 = compress H (parseBlock fun t => p.getD t 0) := by
  rw [compressList_succ, compressList_zero]; simp [blockOf]

theorem hash_eq (m : List Byte) (nt : Nat)
    (hn : (m.length % 64 + 1 + (119 - m.length % 64) % 64 + 8) = 64 * nt) :
    Spec.Md5.hash m = (compressList (compressList H0 m (m.length / 64))
      (rest m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ lenBytes m) nt).toList.flatMap
        wordBytes := by
  have hp : pad m = m ++ ([0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ lenBytes m) := by
    simp [pad, lenBytes, List.append_assoc]
  have hlen : (pad m).length / 64 = m.length / 64 + nt := by
    rw [hp]; simp only [List.length_append, List.length_replicate, lenBytes_length, List.length_singleton]
    omega
  simp only [Spec.Md5.hash]
  rw [hlen, compressList_add, hp, compressList_append (by omega),
    List.drop_append_of_le_length (by omega)]
  simp only [List.append_assoc]

theorem parseBlock_congr {f g : Nat → Byte} (h : ∀ k < 64, f k = g k) : parseBlock f = parseBlock g := by
  funext j
  have := j.isLt
  simp only [parseBlock]
  rw [h _ (by omega), h _ (by omega), h _ (by omega), h _ (by omega)]

/-- A message whose padding takes one more block. -/
theorem hash_one {m : List Byte} (hr : m.length % 64 < 56) :
    Spec.Md5.hash m = (compress (compressList H0 m (m.length / 64))
      (parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (55 - m.length % 64) 0 ++
        lenBytes m).getD t 0)).toList.flatMap wordBytes := by
  rw [hash_eq m 1 (by omega), compressList_one,
    show (119 - m.length % 64) % 64 = 55 - m.length % 64 by omega]

theorem getD_append_right {p q : List Byte} {j : Nat} :
    (p ++ q).getD (p.length + j) 0 = q.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- A message whose padding takes two more blocks. -/
theorem hash_two {m : List Byte} (hr : 56 ≤ m.length % 64) :
    Spec.Md5.hash m = (compress (compress (compressList H0 m (m.length / 64))
      (parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0).getD t 0))
      (parseBlock fun t => (List.replicate 56 0 ++ lenBytes m).getD t 0)).toList.flatMap wordBytes := by
  rw [hash_eq m 2 (by omega), compressList_succ, compressList_one]
  have e : rest m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ lenBytes m =
      (rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0) ++
        (List.replicate 56 0 ++ lenBytes m) := by
    rw [show (119 - m.length % 64) % 64 = (63 - m.length % 64) + 56 by omega, ← List.replicate_append_replicate]
    simp only [List.append_assoc]
  have hl : (rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0).length = 64 := by
    simp only [List.length_append, rest_length, List.length_replicate, List.length_singleton]; omega
  rw [e]
  have h1 : (parseBlock fun t => ((rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0) ++
      (List.replicate 56 0 ++ lenBytes m)).getD t 0) =
      parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0).getD t 0 :=
    parseBlock_congr fun k hk => getD_append_left (by omega)
  have h2 : blockOf ((rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0) ++
      (List.replicate 56 0 ++ lenBytes m)) 1 =
      parseBlock fun t => (List.replicate 56 0 ++ lenBytes m).getD t 0 :=
    parseBlock_congr fun k _ => by
      have := getD_append_right (p := rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0)
        (q := List.replicate 56 0 ++ lenBytes m) (j := k)
      rw [hl] at this
      exact this
  rw [h1, h2]

end VG.Proof.Md5.Stream
