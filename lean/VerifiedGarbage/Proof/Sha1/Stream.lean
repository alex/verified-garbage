import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Set
import Mathlib.Tactic.Use
import Mathlib.Tactic.ByContra
import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Streaming SHA-1: facts about the specification

Untrusted: everything here is checked by Lean. How `Repr` evolves as bytes
are buffered and blocks compressed, and how the padded message decomposes,
independently of any target.
-/

namespace VG.Proof.Sha1.Stream

open VG.Spec.Sha1

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
      ring_nf
    rw [this]

theorem getD_append_left {p q : List Byte} {j : Nat} (h : j < p.length) :
    (p ++ q).getD j 0 = p.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem compressList_append {H : HashValue} {p q : List Byte} {n : Nat} (h : 64 * n ≤ p.length) :
    compressList H (p ++ q) n = compressList H p n :=
  compressList_congr fun _ hj => getD_append_left (by omega)

/-! ## Memory -/

theorem stateAt_congr {mem mem' : Mem} {p : Addr} (h : ∀ i < 20, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i)) :
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

/-- `Repr` only depends on the 84 bytes of the state. -/
theorem repr_congr {mem mem' : Mem} {p : Addr} {m : List Byte}
    (h : ∀ i < 84, mem' (p + BitVec.ofNat 64 i) = mem (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha1.Repr mem p m) : Spec.Sha1.Repr mem' p m := by
  refine ⟨by rw [stateAt_congr fun i hi => h i (by omega)]; exact hr.1, ?_⟩
  rw [← hr.2]
  apply bytesAt_congr
  intro i hi
  have := h (20 + i) (by omega)
  rwa [show p + 20 + BitVec.ofNat 64 i = p + BitVec.ofNat 64 (20 + i) by
    simp only [BitVec.ofNat_add]; rw [BitVec.add_assoc]; rfl]

/-- `m` with the bytes `xs` written from `q` on. -/
def writeBytes (m : Mem) (q : Addr) (xs : List Byte) : Mem :=
  fun a => if (a - q).toNat < xs.length then xs.getD (a - q).toNat 0 else m a

theorem writeBytes_nil (m : Mem) (q : Addr) : writeBytes m q [] = m := by
  funext a; simp [writeBytes]

theorem writeW8_apply (m : Mem) (a x : Addr) (b : Byte) :
    m.writeW a b x = if x = a then b else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have : (x - a).toNat = 0 := by omega
      have : x - a = 0 := BitVec.eq_of_toNat_eq (by simpa using this)
      bv_omega
    simp only [this, h, ite_false]

theorem writeBytes_snoc (m : Mem) (q : Addr) (xs : List Byte) (b : Byte) (h : xs.length < 2 ^ 64) :
    writeBytes m q (xs ++ [b]) = (writeBytes m q xs).writeW (q + BitVec.ofNat 64 xs.length) b := by
  funext a
  rw [writeW8_apply]
  simp only [writeBytes, List.length_append, List.length_singleton]
  by_cases ha : a = q + BitVec.ofNat 64 xs.length
  · subst ha
    rw [show q + BitVec.ofNat 64 xs.length - q = BitVec.ofNat 64 xs.length by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    simp [List.getD_eq_getElem?_getD]
  · have hne : (a - q).toNat ≠ xs.length := by
      intro h'
      apply ha
      have : a - q = BitVec.ofNat 64 xs.length := BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt h])
      bv_omega
    simp only [ha, ite_false]
    by_cases hl : (a - q).toNat < xs.length
    · simp only [show (a - q).toNat < xs.length + 1 by omega, hl, ite_true]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
    · simp only [show ¬ (a - q).toNat < xs.length + 1 by omega, hl, ite_false]

/-- The bytes before `q` (within `2⁶⁴ - |xs|`) are unchanged. -/
theorem writeBytes_before (m : Mem) (q : Addr) (xs : List Byte) {i d : Nat} (hi : i < d)
    (h : d + xs.length < 2 ^ 64) :
    writeBytes m (q + BitVec.ofNat 64 d) xs (q + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  split
  · rename_i hc
    rw [show q + BitVec.ofNat 64 i - (q + BitVec.ofNat 64 d) = BitVec.ofNat 64 i - BitVec.ofNat 64 d by
      bv_omega, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (a := d) (by omega), show 2 ^ 64 - d + i = 2 ^ 64 - (d - i) by omega,
      Nat.mod_eq_of_lt (by omega)] at hc
    omega
  · rfl

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
    rw [show p + BitVec.ofNat 64 (r + j) - (p + BitVec.ofNat 64 r) = BitVec.ofNat 64 j by
      simp only [BitVec.ofNat_add]; bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hj, List.getD_eq_getElem?_getD]

theorem writeBytes_frame (m : Mem) (q : Addr) (xs : List Byte) {R : Region} (hR : R.Contains q xs.length) :
    Frame [R] m (writeBytes m q xs) := by
  intro x hx
  simp only [writeBytes]
  split
  · rename_i h; exact absurd (hR.byte h) (hx R (List.mem_singleton_self _))
  · rfl

/-- A little-endian write is a write of its bytes. -/
theorem write_eq_writeBytes (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) :
    m.write a n v = writeBytes m a ((List.range n).map fun j => v.extractLsb' (8 * j) 8) := by
  funext x
  simp only [Mem.write, writeBytes, List.length_map, List.length_range]
  split
  · rename_i h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
      Option.getD_some]
  · rfl

/-- Writing `ys` right after `xs`. -/
theorem writeBytes_append (m : Mem) (q : Addr) (xs ys : List Byte) (h : xs.length + ys.length < 2 ^ 64) :
    writeBytes (writeBytes m q xs) (q + BitVec.ofNat 64 xs.length) ys = writeBytes m q (xs ++ ys) := by
  funext a
  simp only [writeBytes, List.length_append]
  have hq : (a - (q + BitVec.ofNat 64 xs.length)).toNat =
      ((a - q).toNat + (18446744073709551616 - xs.length)) % 18446744073709551616 := by
    rw [show a - (q + BitVec.ofNat 64 xs.length) = (a - q) - BitVec.ofNat 64 xs.length by bv_omega,
      BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := xs.length) (by omega),
      Nat.add_comm]
  have hlt : (a - q).toNat < 18446744073709551616 := (a - q).isLt
  have h' : xs.length + ys.length < 18446744073709551616 := h
  by_cases h1 : (a - q).toNat < xs.length
  · have ht : ¬ (a - (q + BitVec.ofNat 64 xs.length)).toNat < ys.length := by rw [hq]; omega
    simp only [ht, h1, ite_false, ite_true, show (a - q).toNat < xs.length + ys.length by omega]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · have ht : (a - (q + BitVec.ofNat 64 xs.length)).toNat = (a - q).toNat - xs.length := by rw [hq]; omega
    simp only [ht, h1, ite_false]
    by_cases h2 : (a - q).toNat < xs.length + ys.length
    · simp only [show (a - q).toNat - xs.length < ys.length by omega, h2, ite_true]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : xs.length ≤ (a - q).toNat)]
    · simp only [show ¬ (a - q).toNat - xs.length < ys.length by omega, h2, ite_false]

/-! ## `Repr` -/

theorem repr_nil {mem : Mem} {p : Addr} (h : stateAt mem p = H0) : Spec.Sha1.Repr mem p [] := by
  simp [Spec.Sha1.Repr, h, compressList_zero, bytesAt]

/-- Appending bytes that stay within the buffer. -/
theorem repr_append_buf {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha1.Repr mem p m)
    (hlen : m.length % 64 + xs.length < 64) (hs : stateAt mem' p = stateAt mem p)
    (hb : bytesAt mem' (p + 20) (m.length % 64 + xs.length) = m.drop (64 * (m.length / 64)) ++ xs) :
    Spec.Sha1.Repr mem' p (m ++ xs) := by
  have hdiv : (m ++ xs).length / 64 = m.length / 64 := by simp only [List.length_append]; omega
  have hmod : (m ++ xs).length % 64 = m.length % 64 + xs.length := by
    simp only [List.length_append]; omega
  refine ⟨?_, ?_⟩
  · rw [hs, hr.1, hdiv, compressList_append (by omega)]
  · rw [hmod, hb, hdiv, List.drop_append_of_le_length (by omega)]

/-- Appending bytes that complete a block `B` (whose bytes are the buffered
ones followed by `xs`), which is compressed. -/
theorem repr_append_block {mem mem' : Mem} {p : Addr} {m xs : List Byte} (hr : Spec.Sha1.Repr mem p m)
    (hlen : m.length % 64 + xs.length = 64)
    (hs : stateAt mem' p =
      compress (stateAt mem p) (parseBlock fun k => (m.drop (64 * (m.length / 64)) ++ xs).getD k 0)) :
    Spec.Sha1.Repr mem' p (m ++ xs) := by
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

/-- The message length in bits, as 8 big-endian bytes. -/
def lenBytes (m : List Byte) : List Byte :=
  (List.range 8).reverse.map fun i => (BitVec.ofNat 64 (8 * m.length)).extractLsb' (8 * i) 8

theorem lenBytes_length (m : List Byte) : (lenBytes m).length = 8 := by simp [lenBytes]

theorem shl3 (hi lo : BitVec 32) : (hi <<< 3 ||| lo >>> 29) ++ lo <<< 3 = (hi ++ lo) <<< 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi'
  conv_rhs => rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  rw [BitVec.getLsbD_append]
  by_cases h1 : i < 32
  · simp only [h1, ↓reduceIte]; rw [BitVec.getLsbD_shiftLeft]
    by_cases h3 : i < 3
    · simp [h3]
    · simp only [show i - 3 < 32 by omega, ↓reduceIte]; simp [h1, h3, hi']
  · simp only [h1, ↓reduceIte]; rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    by_cases h35 : i < 35
    · simp only [show i - 3 < 32 by omega, ↓reduceIte]; rw [show 29 + (i - 32) = i - 3 by omega]
      simp [show i - 32 < 3 by omega, show ¬ i < 3 by omega, hi']
    · simp only [show ¬ i - 3 < 32 by omega, ↓reduceIte]; rw [show i - 3 - 32 = i - 32 - 3 by omega]
      have : lo.getLsbD (29 + (i - 32)) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      simp [this, show ¬ i - 32 < 3 by omega, show ¬ i < 3 by omega, show i - 32 < 32 by omega, hi']

theorem bits8 (x : BitVec 64) : BitVec.ofNat 64 (8 * x.toNat) = x <<< 3 := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

/-- The message length in bits, big-endian, from the two halves of the byte count. -/
theorem lenBytes_halves (hi lo : BitVec 32) (m : List Byte) (h : hi ++ lo = BitVec.ofNat 64 m.length) :
    lenBytes m = Spec.Sha1.wordBytes (hi <<< 3 ||| lo >>> 29) ++ Spec.Sha1.wordBytes (lo <<< 3) := by
  have hx : BitVec.ofNat 64 (8 * m.length) = (hi <<< 3 ||| lo >>> 29) ++ lo <<< 3 := by
    rw [shl3, h, ← bits8]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.mul_mod]
  simp only [lenBytes, hx, Spec.Sha1.wordBytes]
  simp only [List.range_succ, List.range_zero, List.nil_append, List.reverse_cons,
    List.reverse_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  refine List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_,
    List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, List.cons_eq_cons.mpr ⟨?_, rfl⟩⟩⟩⟩⟩⟩⟩⟩ <;>
  · ext i hi
    simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_append]
    split <;> first | omega | (congr 1; omega) | rfl

/-- The bytes after the whole blocks of `m`. -/
abbrev rest (m : List Byte) : List Byte := m.drop (64 * (m.length / 64))

theorem rest_length (m : List Byte) : (rest m).length = m.length % 64 := by
  simp only [rest, List.length_drop]; omega

theorem compressList_one (H : HashValue) (p : List Byte) :
    compressList H p 1 = compress H (parseBlock fun t => p.getD t 0) := by
  rw [compressList_succ, compressList_zero]; simp [blockOf]

theorem hash_eq (m : List Byte) (nt : Nat)
    (hn : (m.length % 64 + 1 + (119 - m.length % 64) % 64 + 8) = 64 * nt) :
    Spec.Sha1.hash m = (compressList (compressList H0 m (m.length / 64))
      (rest m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ lenBytes m) nt).toList.flatMap
        wordBytes := by
  have hp : pad m = m ++ ([0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ lenBytes m) := by
    simp [pad, lenBytes, List.append_assoc]
  have hlen : (pad m).length / 64 = m.length / 64 + nt := by
    rw [hp]; simp only [List.length_append, List.length_replicate, lenBytes_length, List.length_singleton]
    omega
  simp only [Spec.Sha1.hash]
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
    Spec.Sha1.hash m = (compress (compressList H0 m (m.length / 64))
      (parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (55 - m.length % 64) 0 ++
        lenBytes m).getD t 0)).toList.flatMap wordBytes := by
  rw [hash_eq m 1 (by omega), compressList_one,
    show (119 - m.length % 64) % 64 = 55 - m.length % 64 by omega]

theorem getD_append_right {p q : List Byte} {j : Nat} :
    (p ++ q).getD (p.length + j) 0 = q.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- A message whose padding takes two more blocks. -/
theorem hash_two {m : List Byte} (hr : 56 ≤ m.length % 64) :
    Spec.Sha1.hash m = (compress (compress (compressList H0 m (m.length / 64))
      (parseBlock fun t => (rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0).getD t 0))
      (parseBlock fun t => (List.replicate 56 0 ++ lenBytes m).getD t 0)).toList.flatMap wordBytes := by
  rw [hash_eq m 2 (by omega), compressList_succ, compressList_one]
  have e : rest m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ lenBytes m =
      (rest m ++ [0x80] ++ List.replicate (63 - m.length % 64) 0) ++
        (List.replicate 56 0 ++ lenBytes m) := by
    rw [show (119 - m.length % 64) % 64 = (63 - m.length % 64) + 56 by omega, List.replicate_add]
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
      simpa using this
  rw [h1, h2]

end VG.Proof.Sha1.Stream
