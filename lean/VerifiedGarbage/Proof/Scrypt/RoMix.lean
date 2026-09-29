import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# scryptROMix: facts about the specification

Untrusted: everything here is checked by Lean. Target-independent facts
about `Spec.Scrypt.roMix`: the blocks `V[i]` step 2 writes (`vList`), step 3
one iteration at a time (`mixLoop_succ_fst`, `mixLoop_succ_snd`), the
lengths of the blocks, and `Integerify (X) mod 2^e` as a little-endian word
read from memory (`integerify_mod`).
-/

namespace VG.Proof.Scrypt

open VG.Spec.Scrypt
open VG.Spec.Pbkdf2 (xorBytes)

/-! ## Step 2: the blocks `V[i]` -/

/-- The blocks `V[0], …, V[N - 1]` that step 2 of scryptROMix writes. -/
abbrev vList (r N : Nat) (b : List Byte) : List (List Byte) :=
  (List.range N).map fun i => Nat.repeat (blockMix r) i b

theorem vList_getD {r N j : Nat} (b : List Byte) (hj : j < N) :
    (vList r N b).getD j [] = Nat.repeat (blockMix r) j b := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl

theorem roMix_eq (r N : Nat) (b : List Byte) :
    roMix r N b = (mixLoop r N (vList r N b) N (Nat.repeat (blockMix r) N b)).1 := rfl

theorem roMixIndices_eq (r N : Nat) (b : List Byte) :
    roMixIndices r N b = (mixLoop r N (vList r N b) N (Nat.repeat (blockMix r) N b)).2 := rfl

/-! ## Step 3, one iteration at a time -/

theorem mixLoop_succ_fst (r N : Nat) (v : List (List Byte)) (n : Nat) (x : List Byte) :
    (mixLoop r N v (n + 1) x).1 =
      (mixLoop r N v n (blockMix r (xorBytes x (v.getD (integerify r x % N) [])))).1 := rfl

theorem mixLoop_succ_snd (r N : Nat) (v : List (List Byte)) (n : Nat) (x : List Byte) :
    (mixLoop r N v (n + 1) x).2 = integerify r x % N ::
      (mixLoop r N v n (blockMix r (xorBytes x (v.getD (integerify r x % N) [])))).2 := rfl

/-! ## Lengths -/

theorem blockMix_length {r : Nat} {b : List Byte} (_h : b.length = 128 * r) :
    (blockMix r b).length = 128 * r := by
  rw [blockMix_eq, List.length_append, length_flatMap_const _ fun _ => yAt_length _ _ _,
    length_flatMap_const _ fun _ => yAt_length _ _ _, List.length_range]
  omega

theorem repeat_blockMix_length {r : Nat} {b : List Byte} (h : b.length = 128 * r) (i : Nat) :
    (Nat.repeat (blockMix r) i b).length = 128 * r := by
  induction i with
  | zero => exact h
  | succ i ih => exact blockMix_length ih

/-! ## `Integerify` -/

theorem bytesAt_length' (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem bytesAt_add' (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, BitVec.ofNat_add, BitVec.add_assoc]

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · rw [BitVec.add_zero]
  · exact List.map_congr_left fun i _ => by
      simp only [Function.comp_apply]
      rw [show p + BitVec.ofNat 64 (i + 1) = p + 1 + BitVec.ofNat 64 i by bv_omega]

/-- `B[i]` of the bytes at `p` is the 64 bytes at `p + 64 i`. -/
theorem blk_bytesAt' (m : Mem) (p : Addr) {n i : Nat} (h : 64 * i + 64 ≤ n) :
    blk (bytesAt m p n) i = bytesAt m (p + BitVec.ofNat 64 (64 * i)) 64 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 64 * i + 64 + k := ⟨n - (64 * i + 64), by omega⟩
  rw [blk, bytesAt_add', bytesAt_add', List.append_assoc, List.drop_left' (bytesAt_length' _ _ _),
    List.take_left' (bytesAt_length' _ _ _)]

theorem leNat_append (xs ys : List Byte) :
    leNat (xs ++ ys) = leNat xs + 256 ^ xs.length * leNat ys := by
  induction xs with
  | nil => simp [leNat]
  | cons x xs ih =>
    simp only [leNat, List.foldr_cons, List.cons_append, List.length_cons] at ih ⊢
    rw [ih, Nat.pow_succ, Nat.mul_add, Nat.add_assoc, Nat.mul_assoc, Nat.mul_left_comm]

theorem toNat_append8 {n : Nat} (x : BitVec n) (y : BitVec 8) :
    (x ++ y).toNat = y.toNat + 256 * x.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]
  omega

/-- The `n` bytes at `a`, read as a little-endian integer, are `m.read a n`. -/
theorem leNat_bytesAt (m : Mem) (a : Addr) (n : Nat) :
    leNat (bytesAt m a n) = (m.read a n).toNat := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [bytesAt_succ, Mem.read, toNat_append8, ← ih]
    rfl

theorem leNat_bytesAt64_mod (m : Mem) (a : Addr) {e : Nat} (he : e ≤ 64) :
    leNat (bytesAt m a 64) % 2 ^ e = (m.readW a 64).toNat % 2 ^ e := by
  rw [show (64 : Nat) = 8 + 56 from rfl, bytesAt_add', leNat_append, bytesAt_length',
    show (256 : Nat) ^ 8 = 2 ^ e * 2 ^ (64 - e) by rw [← Nat.pow_add, Nat.add_sub_cancel' he],
    Nat.mul_assoc, Nat.add_mul_mod_self_left, leNat_bytesAt]
  simp only [Mem.readW, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (BitVec.isLt _)]

/-- `Integerify (X) mod 2^e`, for `e ≤ 64`, is the first 8 bytes of `X`'s last
64-byte block, read little-endian, mod `2^e`. -/
theorem integerify_mod (m : Mem) (p : Addr) {r e : Nat} (hr : 0 < r) (he : e ≤ 64) :
    integerify r (bytesAt m p (128 * r)) % 2 ^ e =
      (m.readW (p + BitVec.ofNat 64 (128 * r - 64)) 64).toNat % 2 ^ e := by
  rw [integerify, blk_bytesAt' _ _ (by omega), show 64 * (2 * r - 1) = 128 * r - 64 by omega,
    leNat_bytesAt64_mod _ _ he]

theorem and_mask (w : BitVec 64) {e : Nat} (he : e ≤ 64) :
    (w &&& BitVec.ofNat 64 (2 ^ e - 1)).toNat = w.toNat % 2 ^ e := by
  have := Nat.pow_le_pow_right (by omega : 0 < 2) he
  have := Nat.one_le_two_pow (n := e)
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]

end VG.Proof.Scrypt
