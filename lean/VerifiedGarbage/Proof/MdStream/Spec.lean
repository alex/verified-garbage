import VerifiedGarbage.Proof.Sha256.Stream

/-!
# Streaming Merkle–Damgård hash functions: facts about the specification

Untrusted: everything here is checked by Lean. MD5, SHA-1, SHA-256 and the
SHA-512 family share one streaming design: the state is the hash value
followed by a one-block buffer, and `finalize` appends `0x80`, zeros and the
message length. `Md B N L` is what their streaming proofs need of one of
them: its block size `B`, the size `N` of its stored hash value (where the
buffer starts in the state), the size `L` of its length field, and its
compression function, padding and digest. The hash functions' own `Repr`,
`pad` and `hash` (in `Spec/`) are these definitions for their instance, by
unfolding. How `Repr` evolves as bytes are buffered and blocks compressed, and
how the padded message decomposes, is proven here once for all of them.
(Memory written byte by byte is `Proof.Sha256.Stream.writeBytes`, which does
not depend on the hash function.)
-/

namespace VG.Proof.MdStream

open VG.Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (getD_append_left getD_append_right bytesAt_congr)

/-- A Merkle–Damgård hash function, as its streaming proofs see it: blocks of
`B` bytes, a stored hash value of `N` bytes, a length field of `L` bytes. -/
structure Md (B N L : Nat) where
  /-- The hash value. -/
  HV : Type
  /-- A message block. -/
  Blk : Type
  /-- The hash value stored at an address (`N` bytes). -/
  stateAt : Mem → Addr → HV
  /-- The block made of bytes `0 … B-1`. -/
  parse : (Nat → Byte) → Blk
  /-- The compression function. -/
  compress : HV → Blk → HV
  /-- The length field of a message of `n` bytes. -/
  lenBytes : Nat → List Byte
  /-- The length field computed from a byte count modulo 2⁶⁴, which is
  `lenBytes` for the lengths `lenOk` accepts. -/
  lenOf : BitVec 64 → List Byte
  /-- The message lengths the byte count determines the length field of. -/
  lenOk : Nat → Prop
  /-- The output of the final hash value. -/
  digest : HV → List Byte
  stateAt_congr : ∀ {mem mem' : Mem} {p : Addr},
    (∀ i < N, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) → stateAt mem' p = stateAt mem p
  parse_congr : ∀ {f g : Nat → Byte}, (∀ k < B, f k = g k) → parse f = parse g
  lenBytes_length : ∀ n, (lenBytes n).length = L
  lenOf_eq : ∀ n, lenOk n → lenOf (BitVec.ofNat 64 n) = lenBytes n
  lenOf_length : ∀ x, (lenOf x).length = L
  digest_length : ∀ h, (digest h).length = N

namespace Md

variable {B N L : Nat} (H : Md B N L)

/-- The block at `p`. -/
def blockAt (m : Mem) (p : Addr) : H.Blk := H.parse fun k => m (p + BitVec.ofNat 64 k)

/-- `h` updated with the `n` consecutive blocks at `p`. -/
def compressBlocks (h : H.HV) (m : Mem) (p : Addr) (n : Nat) : H.HV :=
  (List.range n).foldl (fun h i => H.compress h (H.blockAt m (p + BitVec.ofNat 64 (B * i)))) h

/-- `h` updated with the first `n` blocks of the bytes `p`. -/
def compressList (h : H.HV) (p : List Byte) (n : Nat) : H.HV :=
  (List.range n).foldl (fun h i => H.compress h (H.parse fun k => p.getD (B * i + k) 0)) h

/-- The streaming state at `p` represents the message `m`, hashed from `iv`:
its hash value is `iv` updated with the whole blocks of `m`, and its buffer
starts with the remaining bytes of `m`. -/
def Repr (iv : H.HV) (mem : Mem) (p : Addr) (m : List Byte) : Prop :=
  H.stateAt mem p = H.compressList iv m (m.length / B) ∧
  bytesAt mem (p + BitVec.ofNat 64 N) (m.length % B) = m.drop (B * (m.length / B))

/-- The padded message: `0x80`, the fewest zeros that leave room for the
length field at the end of a block, and the length field. -/
def pad (m : List Byte) : List Byte :=
  m ++ [0x80] ++ List.replicate ((2 * B - L - 1 - m.length % B) % B) 0 ++ H.lenBytes m.length

/-- The final hash value of `m`, hashed from `iv`, as output. -/
def hash (iv : H.HV) (m : List Byte) : List Byte :=
  H.digest (H.compressList iv (H.pad m) ((H.pad m).length / B))

/-- Block `i` of the bytes `p`. -/
def blockOf (p : List Byte) (i : Nat) : H.Blk := H.parse fun k => p.getD (B * i + k) 0

theorem compressBlocks_one (h : H.HV) (m : Mem) (p : Addr) :
    H.compressBlocks h m p 1 = H.compress h (H.blockAt m p) := by
  simp [compressBlocks]

theorem compressList_succ (h : H.HV) (p : List Byte) (n : Nat) :
    H.compressList h p (n + 1) = H.compress (H.compressList h p n) (H.blockOf p n) := by
  simp only [compressList, List.range_succ, List.foldl_append, blockOf, List.foldl_cons, List.foldl_nil]

theorem compressList_zero (h : H.HV) (p : List Byte) : H.compressList h p 0 = h := by
  simp only [compressList, List.range_zero, List.foldl_nil]

theorem compressList_congr {h : H.HV} {p q : List Byte} {n : Nat}
    (hpq : ∀ j < B * n, p.getD j 0 = q.getD j 0) : H.compressList h p n = H.compressList h q n := by
  induction n with
  | zero => simp only [compressList_zero]
  | succ n ih =>
    rw [compressList_succ, compressList_succ, ih fun j hj => hpq j (by rw [Nat.mul_succ] at *; omega)]
    have : H.blockOf p n = H.blockOf q n :=
      H.parse_congr fun k hk => hpq _ (by rw [Nat.mul_succ]; omega)
    rw [this]

theorem compressList_add (h : H.HV) (p : List Byte) (a b : Nat) :
    H.compressList h p (a + b) = H.compressList (H.compressList h p a) (p.drop (B * a)) b := by
  induction b with
  | zero => simp only [Nat.add_zero, compressList_zero]
  | succ b ih =>
    rw [← Nat.add_assoc, compressList_succ, compressList_succ, ih]
    have : H.blockOf p (a + b) = H.blockOf (p.drop (B * a)) b := by
      simp only [blockOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
      simp only [Nat.mul_add, Nat.add_assoc]
    rw [this]

theorem compressList_append {h : H.HV} {p q : List Byte} {n : Nat} (hn : B * n ≤ p.length) :
    H.compressList h (p ++ q) n = H.compressList h p n :=
  H.compressList_congr fun _ hj => getD_append_left (by omega)

theorem compressList_one (h : H.HV) (p : List Byte) :
    H.compressList h p 1 = H.compress h (H.parse fun t => p.getD t 0) := by
  rw [compressList_succ, compressList_zero]; simp [blockOf]

/-! ## Division by the block size -/

theorem add_div_of_lt {n x B : Nat} (h : n % B + x < B) : (n + x) / B = n / B := by
  have e := Nat.div_add_mod n B
  rw [show n + x = B * (n / B) + (n % B + x) by omega, Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt h, Nat.add_zero]

theorem add_mod_of_lt {n x B : Nat} (h : n % B + x < B) : (n + x) % B = n % B + x := by
  have e := Nat.div_add_mod n B
  rw [show n + x = B * (n / B) + (n % B + x) by omega, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

theorem add_div_of_eq {n x B : Nat} (hB : 0 < B) (h : n % B + x = B) : (n + x) / B = n / B + 1 := by
  have e := Nat.div_add_mod n B
  rw [show n + x = B * (n / B) + B by omega, Nat.mul_add_div hB, Nat.div_self hB]

theorem add_mod_of_eq {n x B : Nat} (h : n % B + x = B) : (n + x) % B = 0 := by
  have e := Nat.div_add_mod n B
  rw [show n + x = B * (n / B) + B by omega, Nat.mul_add_mod, Nat.mod_self]

theorem mod_lt' {n B : Nat} (hB : 0 < B) : n % B < B := Nat.mod_lt _ hB

theorem mul_div_le (n B : Nat) : B * (n / B) ≤ n := Nat.mul_div_le n B

/-! ## `Repr` -/

/-- `Repr` only depends on the `N + B` bytes of the state. -/
theorem repr_congr {iv : H.HV} {mem mem' : Mem} {p : Addr} {m : List Byte} (hB : 0 < B)
    (h : ∀ i < N + B, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : H.Repr iv mem p m) : H.Repr iv mem' p m := by
  have hm := mod_lt' (n := m.length) hB
  refine ⟨by rw [H.stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply bytesAt_congr
  intro i hi
  have := h (N + i) (by omega)
  rwa [show p + BitVec.ofNat 64 N + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (N + i) by
    rw [BitVec.ofNat_add, BitVec.add_assoc]]

theorem repr_nil {iv : H.HV} {mem : Mem} {p : Addr} (h : H.stateAt mem p = iv) : H.Repr iv mem p [] := by
  simp [Repr, h, compressList_zero, bytesAt]

/-- Appending bytes that stay within the buffer. -/
theorem repr_append_buf {iv : H.HV} {mem mem' : Mem} {p : Addr} {m xs : List Byte}
    (hr : H.Repr iv mem p m) (hlen : m.length % B + xs.length < B)
    (hs : H.stateAt mem' p = H.stateAt mem p)
    (hb : bytesAt mem' (p + BitVec.ofNat 64 N) (m.length % B + xs.length) =
      m.drop (B * (m.length / B)) ++ xs) :
    H.Repr iv mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / B = m.length / B := by
    simp only [List.length_append]; exact add_div_of_lt hlen
  have hmod : (m ++ xs).length % B = m.length % B + xs.length := by
    simp only [List.length_append]; exact add_mod_of_lt hlen
  have hle := mul_div_le m.length B
  refine ⟨?_, ?_⟩
  · rw [hs, hr.1, hdiv, compressList_append _ hle]
  · rw [hmod, hb, hdiv, List.drop_append_of_le_length hle]

/-- Appending bytes that complete a block (whose bytes are the buffered ones
followed by `xs`), which is compressed. -/
theorem repr_append_block {iv : H.HV} {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hB : 0 < B)
    (hr : H.Repr iv mem p m) (hlen : m.length % B + xs.length = B)
    (hs : H.stateAt mem' p =
      H.compress (H.stateAt mem p) (H.parse fun k => (m.drop (B * (m.length / B)) ++ xs).getD k 0)) :
    H.Repr iv mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / B = m.length / B + 1 := by
    simp only [List.length_append]; exact add_div_of_eq hB hlen
  have hmod : (m ++ xs).length % B = 0 := by
    simp only [List.length_append]; exact add_mod_of_eq hlen
  have hle := mul_div_le m.length B
  refine ⟨?_, ?_⟩
  · have hb : H.blockOf (m ++ xs) (m.length / B) =
        H.parse fun k => (m.drop (B * (m.length / B)) ++ xs).getD k 0 := by
      rw [← List.drop_append_of_le_length hle]
      simp only [blockOf, List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [hs, hr.1, hdiv, compressList_succ, compressList_append _ hle, hb]
  · rw [hmod]
    simp only [bytesAt, List.range_zero, List.map_nil]
    symm; rw [List.drop_eq_nil_iff]
    have e := Nat.div_add_mod (m ++ xs).length B
    rw [hmod, Nat.add_zero] at e
    omega

/-! ## Padding -/

/-- The bytes after the whole blocks of `m`. -/
abbrev rest (B : Nat) (m : List Byte) : List Byte := m.drop (B * (m.length / B))

theorem rest_length (B : Nat) (m : List Byte) : (rest B m).length = m.length % B := by
  simp only [rest, List.length_drop]
  have := Nat.div_add_mod m.length B
  omega

theorem hash_eq (iv : H.HV) (m : List Byte) (nt : Nat) (hB : 0 < B)
    (hn : m.length % B + 1 + (2 * B - L - 1 - m.length % B) % B + L = B * nt) :
    H.hash iv m = H.digest (H.compressList (H.compressList iv m (m.length / B))
      (rest B m ++ [0x80] ++ List.replicate ((2 * B - L - 1 - m.length % B) % B) 0 ++
        H.lenBytes m.length) nt) := by
  have hp : H.pad m = m ++ ([0x80] ++ List.replicate ((2 * B - L - 1 - m.length % B) % B) 0 ++
      H.lenBytes m.length) := by
    simp [pad, List.append_assoc]
  have e := Nat.div_add_mod m.length B
  have hle := mul_div_le m.length B
  have hlen : (H.pad m).length / B = m.length / B + nt := by
    rw [hp]
    simp only [List.length_append, List.length_replicate, H.lenBytes_length, List.length_singleton]
    rw [show m.length + (1 + (2 * B - L - 1 - m.length % B) % B + L) = B * (m.length / B + nt) by
      rw [Nat.mul_add]; omega, Nat.mul_div_cancel_left _ hB]
  simp only [hash]
  rw [hlen, compressList_add, hp, compressList_append _ hle, List.drop_append_of_le_length hle]
  simp only [List.append_assoc]

/-- A message whose padding takes one more block. -/
theorem hash_one {iv : H.HV} {m : List Byte} (hB : 0 < B) (hr : m.length % B + L < B) :
    H.hash iv m = H.digest (H.compress (H.compressList iv m (m.length / B))
      (H.parse fun t => (rest B m ++ [0x80] ++ List.replicate (B - L - 1 - m.length % B) 0 ++
        H.lenBytes m.length).getD t 0)) := by
  have hz : (2 * B - L - 1 - m.length % B) % B = B - L - 1 - m.length % B := by
    rw [show 2 * B - L - 1 - m.length % B = (B - L - 1 - m.length % B) + B by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hash_eq H iv m 1 hB (by rw [hz]; omega), compressList_one, hz]

/-- A message whose padding takes two more blocks. -/
theorem hash_two {iv : H.HV} {m : List Byte} (hB : 0 < B) (hL : L < B) (hr : B ≤ m.length % B + L) :
    H.hash iv m = H.digest (H.compress (H.compress (H.compressList iv m (m.length / B))
      (H.parse fun t => (rest B m ++ [0x80] ++ List.replicate (B - 1 - m.length % B) 0).getD t 0))
      (H.parse fun t => (List.replicate (B - L) 0 ++ H.lenBytes m.length).getD t 0)) := by
  have hm := mod_lt' (n := m.length) hB
  have hz : (2 * B - L - 1 - m.length % B) % B = (B - 1 - m.length % B) + (B - L) := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hash_eq H iv m 2 hB (by rw [hz]; omega), compressList_succ, compressList_one]
  have e : rest B m ++ [0x80] ++ List.replicate ((2 * B - L - 1 - m.length % B) % B) 0 ++
      H.lenBytes m.length =
      (rest B m ++ [0x80] ++ List.replicate (B - 1 - m.length % B) 0) ++
        (List.replicate (B - L) 0 ++ H.lenBytes m.length) := by
    rw [hz, ← List.replicate_append_replicate]
    simp only [List.append_assoc]
  have hl : (rest B m ++ [0x80] ++ List.replicate (B - 1 - m.length % B) 0).length = B := by
    simp only [List.length_append, rest_length, List.length_replicate, List.length_singleton]; omega
  rw [e]
  have h1 : (H.parse fun t => ((rest B m ++ [0x80] ++ List.replicate (B - 1 - m.length % B) 0) ++
      (List.replicate (B - L) 0 ++ H.lenBytes m.length)).getD t 0) =
      H.parse fun t => (rest B m ++ [0x80] ++ List.replicate (B - 1 - m.length % B) 0).getD t 0 :=
    H.parse_congr fun k hk => getD_append_left (by omega)
  have h2 : H.blockOf ((rest B m ++ [0x80] ++ List.replicate (B - 1 - m.length % B) 0) ++
      (List.replicate (B - L) 0 ++ H.lenBytes m.length)) 1 =
      H.parse fun t => (List.replicate (B - L) 0 ++ H.lenBytes m.length).getD t 0 :=
    H.parse_congr fun k _ => by
      have := getD_append_right (p := rest B m ++ [0x80] ++ List.replicate (B - 1 - m.length % B) 0)
        (q := List.replicate (B - L) 0 ++ H.lenBytes m.length) (j := k)
      rw [hl] at this
      simpa using this
  rw [h1, h2]

end Md

end VG.Proof.MdStream
