import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Facts about the ChaCha20 keystream

Untrusted: everything here is checked by Lean. The keystream byte by byte
(`keystream_getD`), the bytes of a state in memory (`serialize_stateAt`),
and incrementing the counter of a state in memory (`stateAt_writeW_counter`).
-/

namespace VG.Proof.ChaCha20

open VG.Spec.ChaCha20 (Word stateAt keystream serialize block bytesAt)

/-- The state `S` with its counter (word 12) advanced by `j`, modulo 2³². -/
def ctr (S : CState) (j : Nat) : CState := S.set 12 (S[12] + BitVec.ofNat 32 j)

theorem ctr_zero (S : CState) : ctr S 0 = S := by
  apply Vector.ext; intro i hi
  simp only [ctr, Vector.getElem_set]
  split <;> simp_all

theorem ctr_succ (S : CState) (j : Nat) :
    (ctr S j).set 12 ((ctr S j)[12] + 1) = ctr S (j + 1) := by
  simp only [ctr, Vector.set_set, Vector.getElem_set_self, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

/-- Element `k` of a concatenation of lists of length `n`. -/
theorem getD_flatMap {α β : Type} (f : α → List β) {n : Nat} (hf : ∀ a, (f a).length = n) (a₀ : α)
    (l : List α) {k : Nat} (hk : k < n * l.length) (d : β) :
    (l.flatMap f).getD k d = (f (l.getD (k / n) a₀)).getD (k % n) d := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => by simp [h] at hk
    rw [List.flatMap_cons]
    by_cases h : k < n
    · rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
      have h' : k < (f a).length := by rw [hf]; exact h
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h',
        List.getElem?_cons_zero, Option.getD_some]
    · have h' : (f a).length ≤ k := by rw [hf]; omega
      have e1 : (f a ++ l.flatMap f).getD k d = (l.flatMap f).getD (k - n) d := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h', hf]
      have hk' : k - n < n * l.length := by
        simp only [List.length_cons, Nat.mul_add_one] at hk; omega
      have e2 : k / n = (k - n) / n + 1 := Nat.div_eq_sub_div hn (by omega)
      have e3 : k % n = (k - n) % n := Nat.mod_eq_sub_mod (by omega)
      rw [e1, ih hk', e2, e3, List.getD_cons_succ]

theorem length_flatMap_const {α β : Type} (f : α → List β) {n : Nat} (hf : ∀ a, (f a).length = n)
    (l : List α) : (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.length_append, ih, hf, List.length_cons, Nat.mul_add_one,
      Nat.add_comm]

theorem length_serialize (S : CState) : (serialize S).length = 64 := by
  rw [serialize, length_flatMap_const _ (n := 4) (fun _ => rfl), Vector.length_toList]

/-- Byte `i` of a serialized state: byte `i % 4` of word `i / 4`. -/
theorem serialize_getD (S : CState) {i : Nat} (hi : i < 64) :
    (serialize S).getD i 0 = S[i / 4].extractLsb' (8 * (i % 4)) 8 := by
  rw [serialize, getD_flatMap _ (n := 4) (fun _ => rfl) 0 _ (by rw [Vector.length_toList]; omega)]
  have h4 : i % 4 < 4 := Nat.mod_lt _ (by omega)
  have e : S.toList.getD (i / 4) 0 = S[i / 4] := by
    simp [List.getD_eq_getElem?_getD, show i / 4 < 16 by omega]
  rw [e]; clear e
  generalize S[i / 4] = w
  generalize i % 4 = j at h4 ⊢
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with h | h | h | h <;> subst h <;> rfl

/-- The bytes of a state in memory. -/
theorem serialize_stateAt (m : Mem) (p : Addr) {i : Nat} (hi : i < 64) :
    (serialize (stateAt m p)).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  rw [serialize_getD _ hi]
  simp only [stateAt, Vector.getElem_ofFn]
  rw [← Mem.readW_byte _ _ (Nat.mod_lt _ (by omega)), BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 3
  omega

/-- The keystream, byte by byte. -/
theorem keystream_getD (S : CState) {n k : Nat} (hk : k < n) :
    (keystream S n).getD k 0 = (serialize (block (ctr S (k / 64)))).getD (k % 64) 0 := by
  simp only [keystream]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, ← List.getD_eq_getElem?_getD]
  rw [getD_flatMap _ (n := 64) (fun _ => length_serialize _) 0 _
    (by rw [List.length_range]; omega)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_range (show k / 64 < (n + 63) / 64 by omega),
    Option.getD_some]
  rfl

theorem length_keystream (S : CState) (n : Nat) : (keystream S n).length = n := by
  simp only [keystream, List.length_take]
  rw [length_flatMap_const _ (n := 64) (fun _ => length_serialize _), List.length_range]
  omega

/-- XORing the keystream into data in memory, byte by byte. -/
theorem bytesAt_xor {m m' : Mem} {p : Addr} {n : Nat} {ks : List Byte} (hks : ks.length = n)
    (h : ∀ k < n, m' (p + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k) ^^^ ks.getD k 0) :
    bytesAt m' p n = List.zipWith (· ^^^ ·) (bytesAt m p n) ks := by
  apply List.ext_getElem
  · simp [bytesAt, hks]
  · intro k h₁ h₂
    simp only [bytesAt, List.length_map, List.length_range] at h₁
    simp only [bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
    rw [h k h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]

end VG.Proof.ChaCha20
