import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Poly1305
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring.RingNF

/-!
# Poly1305: lemmas about the specification

Untrusted: everything here is checked by Lean. Facts about `Spec/Poly1305.lean`
that do not depend on the target: little-endian numbers of byte strings in
memory, the accumulator of a message extended by whole blocks or a last
block, and the tag.
-/

namespace VG.Proof.Poly1305

open VG.Spec.Poly1305

/-! ## Little-endian numbers -/

theorem leNum_append (a b : List Byte) : leNum (a ++ b) = leNum a + 256 ^ a.length * leNum b := by
  induction a with
  | nil => simp [leNum]
  | cons x xs ih => simp only [List.cons_append, leNum, ih, List.length_cons, Nat.pow_succ]; ring

theorem leNum_lt (a : List Byte) : leNum a < 256 ^ a.length := by
  induction a with
  | nil => simp [leNum]
  | cons x xs ih =>
    simp only [leNum, List.length_cons, Nat.pow_succ]
    have := x.isLt
    omega

theorem leNum_replicate_zero (n : Nat) : leNum (List.replicate n (0 : Byte)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, leNum, ih]; rfl

theorem bytesAt_succ (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = m p :: bytesAt m (p + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    show m _ = m _
    congr 1
    rw [BitVec.add_assoc, Nat.succ_eq_add_one, BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 i)]
    rfl

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show m _ = m _
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

theorem leNum_bytesAt_read (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p n) = (m.read p n).toNat := by
  induction n generalizing p with
  | zero => simp [bytesAt, leNum, Mem.read]
  | succ n ih =>
    rw [bytesAt_succ, leNum, ih, Mem.read, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt, Nat.shiftLeft_eq]
    ring

theorem leNum_bytesAt_64 (m : Mem) (p : Addr) : leNum (bytesAt m p 8) = (m.readW p 64).toNat := by
  rw [leNum_bytesAt_read]
  simp [Mem.readW]

/-- A number stored as three little-endian 64-bit words. -/
theorem leNum_bytesAt_24 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 24) = (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat +
      2 ^ 128 * (m.readW (p + 16) 64).toNat := by
  rw [show 24 = 8 + (8 + 8) from rfl, bytesAt_add, bytesAt_add, leNum_append, leNum_append,
    length_bytesAt, length_bytesAt, leNum_bytesAt_64, leNum_bytesAt_64, leNum_bytesAt_64,
    BitVec.add_assoc]
  norm_num
  ring_nf
  rfl

theorem leNum_bytesAt_16 (m : Mem) (p : Addr) :
    leNum (bytesAt m p 16) = (m.readW p 64).toNat + 2 ^ 64 * (m.readW (p + 8) 64).toNat := by
  rw [show 16 = 8 + 8 from rfl, bytesAt_add, leNum_append, length_bytesAt, leNum_bytesAt_64,
    leNum_bytesAt_64]
  norm_num
  rfl

/-! ## The accumulator -/

theorem block_append_left {a b : List Byte} (ha : a.length % 16 = 0) {i : Nat}
    (hi : i < a.length / 16) : block (a ++ b) i = block a i := by
  simp only [block]
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length]
  simp only [List.length_drop]; omega

theorem block_append_right {a b : List Byte} (ha : a.length % 16 = 0) (j : Nat) :
    block (a ++ b) (a.length / 16 + j) = block b j := by
  simp only [block]
  rw [show 16 * (a.length / 16 + j) = a.length + 16 * j by omega, List.drop_append,
    List.drop_of_length_le (by omega), List.nil_append, Nat.add_sub_cancel_left]

theorem numBlocks_append {a b : List Byte} (ha : a.length % 16 = 0) :
    numBlocks (a ++ b) = a.length / 16 + numBlocks b := by
  simp only [numBlocks, List.length_append]; omega

/-- The loop of `accumulate` from the accumulator `a`. -/
def absorbAll (r a : Nat) (msg : List Byte) : Nat :=
  (List.range (numBlocks msg)).foldl (fun a i => (r * (a + leNum (block msg i ++ [0x01]))) % P) a

theorem accumulate_eq (r : Nat) (msg : List Byte) : accumulate r msg = absorbAll r 0 msg := rfl

theorem foldl_congr_mem {α β : Type} {f g : α → β → α} {l : List β} (a : α)
    (h : ∀ x y, y ∈ l → f x y = g x y) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rw [h a y List.mem_cons_self]
    exact ih _ fun x z hz => h x z (List.mem_cons_of_mem _ hz)

theorem absorbAll_append {r a : Nat} {x y : List Byte} (hx : x.length % 16 = 0) :
    absorbAll r a (x ++ y) = absorbAll r (absorbAll r a x) y := by
  have hn : numBlocks x = x.length / 16 := by simp only [numBlocks]; omega
  have e : (List.range (x.length / 16)).foldl
      (fun b i => (r * (b + leNum (block (x ++ y) i ++ [0x01]))) % P) a = absorbAll r a x := by
    rw [absorbAll, hn]
    exact foldl_congr_mem a fun b i hi => by rw [block_append_left hx (List.mem_range.mp hi)]
  rw [absorbAll, numBlocks_append hx, List.range_add, List.foldl_append, List.foldl_map, e, absorbAll]
  exact foldl_congr_mem _ fun b j _ => by rw [block_append_right hx]

theorem accumulate_append {r : Nat} {a b : List Byte} (ha : a.length % 16 = 0) :
    accumulate r (a ++ b) = absorbAll r (accumulate r a) b := by
  rw [accumulate_eq, accumulate_eq, absorbAll_append ha]

/-- Absorbing one block, of 1 to 16 bytes. -/
theorem absorbAll_block {r a : Nat} {b : List Byte} (h₁ : 0 < b.length) (h₂ : b.length ≤ 16) :
    absorbAll r a b = (r * (a + leNum (b ++ [0x01]))) % P := by
  have hn : numBlocks b = 1 := by simp only [numBlocks]; omega
  simp only [absorbAll, hn, List.range_one, List.foldl_cons, List.foldl_nil, block, Nat.mul_zero,
    List.drop_zero]
  rw [List.take_of_length_le h₂]

theorem absorbAll_nil (r a : Nat) : absorbAll r a [] = a := rfl

theorem accumulate_append_block {r : Nat} {a b : List Byte} (ha : a.length % 16 = 0)
    (h₁ : 0 < b.length) (h₂ : b.length ≤ 16) :
    accumulate r (a ++ b) = (r * (accumulate r a + leNum (b ++ [0x01]))) % P := by
  rw [accumulate_append ha, absorbAll_block h₁ h₂]

theorem absorbAll_lt {r a : Nat} (ha : a < P) (msg : List Byte) : absorbAll r a msg < P := by
  rw [absorbAll]
  generalize numBlocks msg = n
  induction n with
  | zero => exact ha
  | succ n _ =>
    rw [List.range_succ, List.foldl_append]
    exact Nat.mod_lt _ (by simp [P])

theorem accumulate_lt (r : Nat) (msg : List Byte) : accumulate r msg < P :=
  absorbAll_lt (by simp [P]) msg

/-! ## Clamping `r` -/

theorem land_split {a b c d : Nat} (ha : a < 2 ^ 64) (hc : c < 2 ^ 64) :
    (a + 2 ^ 64 * b) &&& (c + 2 ^ 64 * d) = (a &&& c) + 2 ^ 64 * (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hac : (a &&& c) < 2 ^ 64 := Nat.lt_of_le_of_lt Nat.and_le_left ha
  rw [Nat.testBit_and]
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c)]
  rw [Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hc,
    Nat.testBit_two_pow_mul_add _ hac]
  split <;> simp [Nat.testBit_and]

/-- The clamped `r` of a key stored as two little-endian 64-bit words. -/
theorem clamp_words (k0 k1 : BitVec 64) :
    clamp (k0.toNat + 2 ^ 64 * k1.toNat) =
      (k0 &&& 0x0ffffffc0fffffff).toNat + 2 ^ 64 * (k1 &&& 0x0ffffffc0ffffffc).toNat := by
  rw [clamp, show (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) =
    0x0ffffffc0fffffff + 2 ^ 64 * 0x0ffffffc0ffffffc by norm_num,
    land_split k0.isLt (by norm_num), BitVec.toNat_and, BitVec.toNat_and]
  rfl

/-! ## The tag -/

theorem leBytes_add (a b x : Nat) :
    leBytes (a + b) x = leBytes a x ++ leBytes b (x / 256 ^ a) := by
  simp only [leBytes, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem leBytes_mod (n x : Nat) : leBytes n (x % 256 ^ n) = leBytes n x := by
  simp only [leBytes]
  apply List.map_congr_left
  intro i hi
  have hi := List.mem_range.mp hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show 256 ^ n = 256 ^ i * 256 ^ (n - i) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  rw [show (2 : Nat) ^ 8 = 256 by norm_num]
  exact dvd_pow_self 256 (by omega)

theorem leBytes_succ (n x : Nat) : leBytes (n + 1) x = BitVec.ofNat 8 x :: leBytes n (x / 256) := by
  rw [Nat.add_comm, leBytes_add, Nat.pow_one]; simp [leBytes]

theorem bytesAt_leBytes (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n = leBytes n (m.read p n).toNat := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have e : (m.read p (n + 1)).toNat = (m.read (p + 1) n).toNat * 256 + (m p).toNat := by
      rw [Mem.read, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (m p).isLt,
        Nat.shiftLeft_eq]
    rw [bytesAt_succ, leBytes_succ, ih, e]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      have := (m p).isLt
      omega
    · congr 1
      have := (m p).isLt
      omega

theorem bytesAt_leBytes_64 (m : Mem) (p : Addr) :
    bytesAt m p 8 = leBytes 8 (m.readW p 64).toNat := by
  rw [bytesAt_leBytes]; simp [Mem.readW]

/-- Two little-endian 64-bit words in memory are the 16 bytes of `x`, if they
are its low 128 bits. -/
theorem bytesAt_leBytes_16 (m : Mem) (p : Addr) (x : Nat)
    (h₀ : (m.readW p 64).toNat = x % 2 ^ 64)
    (h₁ : (m.readW (p + BitVec.ofNat 64 8) 64).toNat = x / 2 ^ 64 % 2 ^ 64) :
    bytesAt m p 16 = leBytes 16 x := by
  rw [show 16 = 8 + 8 from rfl, bytesAt_add, bytesAt_leBytes_64, bytesAt_leBytes_64, h₀, h₁,
    leBytes_add, show (2 : Nat) ^ 64 = 256 ^ 8 by norm_num, leBytes_mod, leBytes_mod]

end VG.Proof.Poly1305
