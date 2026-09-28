import VerifiedGarbage.Spec.Aes

/-!
# The key expansion, word by word

Untrusted: everything here is checked by Lean.

`expandWords key nk i` only ever appends: word `j` is the same in every
prefix that has it (`kw`), each word is 4 bytes when the key is `4 nk`
bytes, and word `i ≥ nk` is `w[i − nk] ⊕ temp` byte by byte, with `temp`
as §5.2 computes it from `w[i − 1]`.
-/

namespace VG.Proof.Aes

open VG VG.Spec.Aes

/-- Word `j` of the schedule of `key`. -/
def kw (key : List Byte) (nk j : Nat) : Word := (expandWords key nk (j + 1)).getD j []

/-- §5.2's `temp` for word `i`, from `w[i − 1]`. -/
def kTemp (nk i : Nat) (prev : Word) : Word :=
  if i % nk = 0 then xorWord (subWord (rotWord prev)) (rcon (i / nk))
  else if nk > 6 ∧ i % nk = 4 then subWord prev
  else prev

theorem expandWords_succ (key : List Byte) (nk i : Nat) :
    expandWords key nk (i + 1) = expandWords key nk i ++ [kw key nk i] := by
  have hl : (expandWords key nk i).length = i := by
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [expandWords]
      split <;> simp [ih]
  have h : ∀ (ws : List Word) (x : Word), ws.length = i → (ws ++ [x]).getD i [] = x := by
    intro ws x h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), h, Nat.sub_self]
    rfl
  unfold kw
  simp only [expandWords]
  split <;> rw [h _ _ hl]

theorem expandWords_length (key : List Byte) (nk i : Nat) : (expandWords key nk i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [expandWords_succ, List.length_append, ih, List.length_singleton]

theorem expandWords_getD (key : List Byte) (nk : Nat) {i j : Nat} (h : j < i) :
    (expandWords key nk i).getD j [] = kw key nk j := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [expandWords_succ]
    by_cases hj : j < i
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [expandWords_length]; omega),
        ← List.getD_eq_getElem?_getD, ih hj]
    · obtain rfl : j = i := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq (expandWords_length ..)),
        expandWords_length, Nat.sub_self]
      rfl

/-- The key's words. -/
theorem kw_key (key : List Byte) {nk i : Nat} (h : i < nk) : kw key nk i = (key.drop (4 * i)).take 4 := by
  show (expandWords key nk (i + 1)).getD i [] = _
  rw [expandWords]
  simp only [h, ite_true]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq (expandWords_length ..)),
    expandWords_length, Nat.sub_self]
  rfl

/-- The other words. -/
theorem kw_step (key : List Byte) {nk i : Nat} (h0 : 0 < nk) (h : nk ≤ i) :
    kw key nk i = xorWord (kw key nk (i - nk)) (kTemp nk i (kw key nk (i - 1))) := by
  show (expandWords key nk (i + 1)).getD i [] = _
  rw [expandWords]
  simp only [show ¬ i < nk by omega, ite_false]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_of_eq (expandWords_length ..)),
    expandWords_length, Nat.sub_self, expandWords_getD key nk (show i - 1 < i by omega),
    expandWords_getD key nk (show i - nk < i by omega)]
  rfl

theorem xorWord_length (a b : Word) : (xorWord a b).length = min a.length b.length := by
  simp [xorWord]

theorem rotWord_length {w : Word} (h : w.length = 4) : (rotWord w).length = 4 := by
  simp [rotWord, h]

theorem kTemp_length {nk i : Nat} {w : Word} (h : w.length = 4) : (kTemp nk i w).length = 4 := by
  unfold kTemp
  split
  · rw [xorWord_length]; simp [subWord, rotWord_length h, rcon]
  · split
    · simp [subWord, h]
    · exact h

/-- Every word is 4 bytes. -/
theorem kw_length {key : List Byte} {nk : Nat} (hk : key.length = 4 * nk) (h0 : 0 < nk) (i : Nat) :
    (kw key nk i).length = 4 := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    by_cases h : i < nk
    · rw [kw_key key h]; simp [hk]; omega
    · rw [kw_step key h0 (by omega), xorWord_length, ih _ (by omega), kTemp_length (ih _ (by omega))]
      rfl

theorem xorWord_getD {a b : Word} (ha : a.length = 4) (hb : b.length = 4) {t : Nat} (ht : t < 4) :
    (xorWord a b).getD t 0 = a.getD t 0 ^^^ b.getD t 0 := by
  simp only [xorWord, List.getD_eq_getElem?_getD, List.getElem?_zipWith]
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
  rfl

theorem subWord_getD {w : Word} {t : Nat} (ht : t < w.length) :
    (subWord w).getD t 0 = sbox (w.getD t 0) := by
  simp only [subWord, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem ht]
  rfl

theorem word4 {w : Word} (h : w.length = 4) : w = [w.getD 0 0, w.getD 1 0, w.getD 2 0, w.getD 3 0] := by
  match w, h with
  | [_, _, _, _], _ => rfl

theorem rotWord_getD {w : Word} (h : w.length = 4) {t : Nat} (ht : t < 4) :
    (rotWord w).getD t 0 = w.getD ((t + 1) % 4) 0 := by
  rw [word4 h]
  rcases t with _ | _ | _ | _ | t
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

theorem rcon_getD (j : Nat) {t : Nat} (ht : t < 4) :
    (rcon j).getD t 0 = if t = 0 then Nat.repeat xtimes (j - 1) 1 else 0 := by
  rcases t with _ | _ | _ | _ | t
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

/-- The schedule, from its words. -/
theorem flatten_expandWords {key : List Byte} {nk : Nat} (hk : key.length = 4 * nk) (h0 : 0 < nk)
    (n : Nat) (f : Nat → Byte) (hf : ∀ k < 4 * n, f k = (kw key nk (k / 4)).getD (k % 4) 0) :
    (List.range (4 * n)).map f = (expandWords key nk n).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [expandWords_succ, List.flatten_append, List.flatten_singleton,
      ← ih fun k hk => hf k (by omega), show 4 * (n + 1) = 4 * n + 4 by omega, List.range_add,
      List.map_append, List.map_map, word4 (kw_length hk h0 n)]
    refine congrArg (_ ++ ·) ?_
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, Function.comp]
    rw [hf _ (by omega), hf _ (by omega), hf _ (by omega), hf _ (by omega)]
    simp only [show (4 * n + 0) / 4 = n by omega, show (4 * n + 1) / 4 = n by omega,
      show (4 * n + 2) / 4 = n by omega, show (4 * n + 3) / 4 = n by omega,
      show (4 * n + 0) % 4 = 0 by omega, show (4 * n + 1) % 4 = 1 by omega,
      show (4 * n + 2) % 4 = 2 by omega, show (4 * n + 3) % 4 = 3 by omega]

end VG.Proof.Aes
