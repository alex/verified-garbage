import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Cipher
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Aes.X86_64.AesNi

/-!
# AES key expansion as 32-bit words

Untrusted: everything here is checked by Lean. `W m kp nk i` is word `w[i]`
of the key schedule of the `nk`-word key at `kp`, as the 32-bit value whose
bytes, least significant first, are the word's bytes (`wv`), which is how a
doubleword of an SSE register holds it. `expandKey_eq`: FIPS 197's
`KEYEXPANSION` is these words, in order; `bytesAt_eq`: memory holding them
as little-endian doublewords holds the schedule.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Spec.Aes (Word subWord rotWord rcon xorWord expandWords expandKey bytesAt rounds)

/-- The bytes of a word, least significant first. -/
def wv (d : BitVec 32) : Word := (List.range 4).map fun j => d.extractLsb' (8 * j) 8

/-- `SUBWORD`, as `aeskeygenassist` computes it. -/
def sub32 (x : BitVec 32) : BitVec 32 :=
  aesSbox (x.extractLsb' 24 8) ++ aesSbox (x.extractLsb' 16 8) ++
    aesSbox (x.extractLsb' 8 8) ++ aesSbox (x.extractLsb' 0 8)

/-- `temp` of `KEYEXPANSION` for word `i`, from `w[i − 1]`. -/
def temp32 (nk i : Nat) (x : BitVec 32) : BitVec 32 :=
  if i % nk = 0 then (sub32 x).rotateRight 8 ^^^ (Impl.Aes.X86_64.AesNi.rc (i / nk)).setWidth 32
  else if nk > 6 ∧ i % nk = 4 then sub32 x else x

/-- Word `i` of the key schedule of the `nk`-word key at `kp`. -/
def W (m : Mem) (kp : Addr) (nk : Nat) (i : Nat) : BitVec 32 :=
  if i < nk ∨ nk = 0 then m.readW (kp + BitVec.ofNat 64 (4 * i)) 32
  else W m kp nk (i - nk) ^^^ temp32 nk i (W m kp nk (i - 1))
termination_by i
decreasing_by all_goals omega

theorem W_lt {m : Mem} {kp : Addr} {nk i : Nat} (h : i < nk) :
    W m kp nk i = m.readW (kp + BitVec.ofNat 64 (4 * i)) 32 := by
  rw [W]; simp [h]

theorem W_ge {m : Mem} {kp : Addr} {nk i : Nat} (h0 : 0 < nk) (h : nk ≤ i) :
    W m kp nk i = W m kp nk (i - nk) ^^^ temp32 nk i (W m kp nk (i - 1)) := by
  rw [W]; simp only [show ¬ (i < nk ∨ nk = 0) by omega, ite_false]

/-! ## Words and bytes -/

theorem wv_eq (d : BitVec 32) :
    wv d = [d.extractLsb' 0 8, d.extractLsb' 8 8, d.extractLsb' 16 8, d.extractLsb' 24 8] := rfl

theorem extract_xor (a b : BitVec 32) (k : Nat) :
    (a ^^^ b).extractLsb' k 8 = a.extractLsb' k 8 ^^^ b.extractLsb' k 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

theorem wv_xor (a b : BitVec 32) : wv (a ^^^ b) = xorWord (wv a) (wv b) := by
  simp only [wv_eq, extract_xor, xorWord, List.zipWith_cons_cons, List.zipWith_nil_left]

theorem extract_cat (a b c d : BitVec 8) :
    (a ++ b ++ c ++ d).extractLsb' 0 8 = d ∧ (a ++ b ++ c ++ d).extractLsb' 8 8 = c ∧
      (a ++ b ++ c ++ d).extractLsb' 16 8 = b ∧ (a ++ b ++ c ++ d).extractLsb' 24 8 = a := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
    simp (disch := omega) only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi, decide_true,
      Bool.true_and, ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem rot_cat (a b c d : BitVec 8) : (a ++ b ++ c ++ d).rotateRight 8 = d ++ a ++ b ++ c := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi' : i < 32 := hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_append, hi', decide_true, Bool.true_and]
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i) with h | h | h | h <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right] <;>
    exact congrArg _ (by omega)

theorem wv_cat (a b c d : BitVec 8) : wv (a ++ b ++ c ++ d) = [d, c, b, a] := by
  obtain ⟨e0, e1, e2, e3⟩ := extract_cat a b c d
  rw [wv_eq, e0, e1, e2, e3]

theorem sub_wv (x : BitVec 32) : subWord (wv x) = wv (sub32 x) := by
  rw [sub32, wv_cat, wv_eq, subWord, sbox_eq]; rfl

theorem subRot_wv (x : BitVec 32) : subWord (rotWord (wv x)) = wv ((sub32 x).rotateRight 8) := by
  rw [sub32, rot_cat, wv_cat, wv_eq, rotWord, subWord, sbox_eq]; rfl

theorem rcon_wv (j : Nat) : rcon j = wv ((Impl.Aes.X86_64.AesNi.rc j).setWidth 32) := by
  rw [show (Impl.Aes.X86_64.AesNi.rc j).setWidth 32 = 0#8 ++ 0#8 ++ 0#8 ++ Impl.Aes.X86_64.AesNi.rc j by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_zero]
    by_cases h : i < 8
    · simp [h]; omega
    · simp [h]; exact fun _ => BitVec.getLsbD_of_ge _ _ (by omega), wv_cat]
  rfl

theorem temp_wv (nk i : Nat) (x : BitVec 32) :
    (if i % nk = 0 then xorWord (subWord (rotWord (wv x))) (rcon (i / nk))
      else if nk > 6 ∧ i % nk = 4 then subWord (wv x) else wv x) = wv (temp32 nk i x) := by
  unfold temp32
  by_cases h1 : i % nk = 0
  · simp only [h1, ite_true, wv_xor, subRot_wv, rcon_wv]
  · by_cases h2 : nk > 6 ∧ i % nk = 4
    · have h2' : (nk > 6 ∧ i % nk = 4) = True := eq_true h2
      simp only [h1, h2', ite_true, ite_false, sub_wv]
    · simp only [h1, h2, ite_false]

/-! ## The key and the schedule -/

theorem getD_mapRange {α : Type} (f : Nat → α) {n i : Nat} (d : α) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD, h]

theorem ofNat_add' (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 (a + b) = p + BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- Word `i` of the key. -/
theorem keyWord (m : Mem) (kp : Addr) {L i : Nat} (h : 4 * i + 4 ≤ L) :
    ((bytesAt m kp L).drop (4 * i)).take 4 = wv (m.readW (kp + BitVec.ofNat 64 (4 * i)) 32) := by
  apply List.ext_getElem
  · simp [bytesAt, wv]; omega
  · intro j h₁ h₂
    have hj : j < 4 := by simpa [wv] using h₂
    simp only [List.getElem_take, List.getElem_drop, bytesAt, List.getElem_map, List.getElem_range,
      wv]
    rw [ofNat_add', Mem.readW_byte m (kp + BitVec.ofNat 64 (4 * i)) hj]

theorem expandWords_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    ∀ n, expandWords (bytesAt m kp (4 * nk)) nk n = (List.range n).map fun i => wv (W m kp nk i)
  | 0 => rfl
  | i + 1 => by
    rw [expandWords, expandWords_eq m kp h0 i, List.range_succ, List.map_append, List.map_singleton]
    by_cases h : i < nk
    · simp only [h, ite_true]
      rw [keyWord _ _ (by omega), W_lt h]
    · simp only [h, ite_false]
      rw [getD_mapRange _ _ (by omega), getD_mapRange _ _ (by omega), temp_wv, ← wv_xor,
        ← W_ge h0 (by omega)]

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp [bytesAt]

/-- `KEYEXPANSION`, as words. -/
theorem expandKey_eq (m : Mem) (kp : Addr) {nk : Nat} (h0 : 0 < nk) :
    expandKey (bytesAt m kp (4 * nk)) =
      ((List.range (4 * (rounds nk + 1))).map fun i => wv (W m kp nk i)).flatten := by
  rw [expandKey, length_bytesAt, show 4 * nk / 4 = nk by omega, expandWords_eq m kp h0]

/-- Memory holding the words `f 0 … f (K − 1)` as little-endian doublewords. -/
theorem bytesAt_eq (m : Mem) (p : Addr) (f : Nat → BitVec 32) :
    ∀ K, (∀ i < K, m.readW (p + BitVec.ofNat 64 (4 * i)) 32 = f i) →
      bytesAt m p (4 * K) = ((List.range K).map fun i => wv (f i)).flatten
  | 0, _ => rfl
  | K + 1, h => by
    rw [List.range_succ, List.map_append, List.flatten_append, ← bytesAt_eq m p f K
      fun i hi => h i (by omega), List.map_singleton, List.flatten_singleton, ← h K (by omega),
      show 4 * (K + 1) = 4 * K + 4 by omega, bytesAt, bytesAt, List.range_add, List.map_append,
      List.map_map]
    congr 1
    simp only [wv]
    refine List.map_congr_left fun j hj => ?_
    simp only [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [ofNat_add', Mem.readW_byte m (p + BitVec.ofNat 64 (4 * K)) hj]

end VG.Proof.Aes.X86_64.AesNi
