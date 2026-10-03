import VerifiedGarbage.Spec.Siv
import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.Proof.Cmac.Stream

/-!
# AES-SIV: lemmas about the specification

How the implementations compute the functions of `Spec/Siv.lean`:

* `cmacWith_split`: CMAC with given subkeys (`cmacWith`) of a message of
  whole blocks followed by its last bytes is the cipher of the chaining value
  of the whole blocks XORed with the last block, as `vg_cmac_aes_update` and
  `vg_cmac_aes_finalize` compute it (`Proof.Cmac.macFull_split` for the
  subkeys of the cipher).
* `s2vFinish_long` and `s2vFinish_short`: the string whose CMAC finishes S2V,
  split as the implementations form it: the first `a` bytes of the last
  string followed by the rest with `D` XORed into its last 16 bytes, for a
  string of at least 16 bytes; `pad(Sₙ) XOR dbl(D)`, one block, otherwise.
* `ctr_getD`: each byte of CTR's output is the byte of the input XORed with
  the byte of the keystream block of its block index.
-/

namespace VG.Proof.Siv

open VG
open VG.Spec.Cmac (chain blocks lastBlock zeros)

/-! ## CMAC with given subkeys -/

/-- SP 800-38B §6.2 steps 3–6 with the subkeys `k1` and `k2`, for a message of
whole blocks `msg` followed by `last`. -/
theorem cmacWith_split (ciph : Spec.Cmac.Cipher) (k1 k2 : List Byte) {msg last : List Byte}
    (hm : msg.length % 16 = 0) (hl : last.length ≤ 16) (hne : msg = [] ∨ 0 < last.length) :
    Spec.Siv.cmacWith ciph k1 k2 (msg ++ last) =
      ciph (Spec.Cmac.xor (chain ciph (zeros 16) (blocks 16 msg)) (lastBlock 16 k1 k2 last)) := by
  obtain ⟨q, hq⟩ : ∃ q, msg.length = 16 * q := ⟨msg.length / 16, by omega⟩
  have hn : (if (msg ++ last).length = 0 then 1 else ((msg ++ last).length + 16 - 1) / 16) = q + 1 := by
    rw [List.length_append]
    split
    · omega
    · have hl0 : 0 < last.length := by
        rcases hne with h | h
        · subst h; simp only [List.length_nil] at *; omega
        · exact h
      omega
  simp only [Spec.Siv.cmacWith, hn, Nat.add_sub_cancel]
  rw [Proof.Cmac.blocks_eq hm last q hq, Proof.Cmac.chain_append, Proof.Cmac.chain_single,
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]

/-- A message of whole blocks, then more whole blocks, then its last bytes. -/
theorem cmacWith_split₂ (ciph : Spec.Cmac.Cipher) (k1 k2 : List Byte) {a b last : List Byte}
    (ha : a.length % 16 = 0) (hb : b.length % 16 = 0) (hl : last.length ≤ 16)
    (hne : a ++ b = [] ∨ 0 < last.length) :
    Spec.Siv.cmacWith ciph k1 k2 (a ++ b ++ last) =
      ciph (Spec.Cmac.xor (chain ciph (chain ciph (zeros 16) (blocks 16 a)) (blocks 16 b))
        (lastBlock 16 k1 k2 last)) := by
  rw [cmacWith_split ciph k1 k2 (by simp [List.length_append]; omega) hl hne,
    Proof.Cmac.Stream.blocks_append ha, Proof.Cmac.chain_append]

/-- The CMAC of a string `S`: the chaining value of its whole blocks but its
last 1 to 16 bytes (`chainedLen 16 L` bytes; none of the empty string), and
the rest. -/
theorem cmacWith_chained (ciph : Spec.Cmac.Cipher) (k1 k2 S : List Byte) :
    Spec.Siv.cmacWith ciph k1 k2 S =
      ciph (Spec.Cmac.xor (chain ciph (zeros 16) (blocks 16 (S.take (Spec.Cmac.chainedLen 16 S.length))))
        (lastBlock 16 k1 k2 (S.drop (Spec.Cmac.chainedLen 16 S.length)))) := by
  conv => lhs; rw [← List.take_append_drop (Spec.Cmac.chainedLen 16 S.length) S]
  have hc := Proof.Cmac.Stream.chainedLen_add_held S.length
  have hh := Proof.Cmac.Stream.held_le S.length
  refine cmacWith_split ciph k1 k2 ?_ ?_ ?_
  · rw [List.length_take, Nat.min_eq_left (by omega)]; exact Proof.Cmac.Stream.chainedLen_mod _
  · rw [List.length_drop]; unfold Proof.Cmac.Stream.held at hh; omega
  · by_cases h0 : S.length = 0
    · left; simp [List.length_eq_zero_iff.mp h0]
    · right
      have := Proof.Cmac.Stream.held_pos (Nat.pos_of_ne_zero h0)
      rw [List.length_drop]; unfold Proof.Cmac.Stream.held at this; omega

/-! ## Finishing S2V -/

theorem length_xor (a b : List Byte) : (Spec.Siv.xor a b).length = min a.length b.length := by
  simp [Spec.Siv.xor]

theorem xor_eq (a b : List Byte) : Spec.Siv.xor a b = Spec.Cmac.xor a b := rfl

/-- `S xorend D`, for any `a ≤ len(S) − len(D)`: the first `a` bytes of `S`,
followed by the rest of `S` xorend `D`. -/
theorem xorend_split (s d : List Byte) {a : Nat} (ha : a + d.length ≤ s.length) :
    Spec.Siv.xorend s d = s.take a ++ Spec.Siv.xorend (s.drop a) d := by
  simp only [Spec.Siv.xorend, List.length_drop, List.drop_drop, List.take_drop]
  have e : a + (s.length - a - d.length) = s.length - d.length := by omega
  rw [e, ← List.append_assoc]
  congr 1
  conv => lhs; rw [← List.take_append_drop a (s.take (s.length - d.length))]
  rw [List.take_take, Nat.min_eq_left (by omega)]

/-- S2V's end for a last string `P` of at least 16 bytes, split at any
`a ≤ len(P) − 16`: the CMAC of the first `a` bytes of `P` followed by the
rest of `P` xorend `D`. -/
theorem s2vFinish_long (mac : List Byte → List Byte) {d P : List Byte} (hd : d.length = 16)
    {a : Nat} (ha : a + 16 ≤ P.length) :
    Spec.Siv.s2vFinish mac d P = mac (P.take a ++ Spec.Siv.xorend (P.drop a) d) := by
  rw [Spec.Siv.s2vFinish, ite_eq_left_of_eq_true _ _ (eq_true (show P.length ≥ 16 by omega)), xorend_split P d (a := a) (by omega)]

/-- S2V's end for a last string `P` shorter than 16 bytes. -/
theorem s2vFinish_short (mac : List Byte → List Byte) (d : List Byte) {P : List Byte}
    (hL : P.length < 16) :
    Spec.Siv.s2vFinish mac d P = mac (Spec.Siv.xor (Spec.Siv.dbl d) (Spec.Siv.pad P)) := by
  rw [Spec.Siv.s2vFinish, ite_eq_right_of_eq_false _ _ (eq_false (show ¬ P.length ≥ 16 by omega))]

theorem length_pad {P : List Byte} (hL : P.length < 16) : (Spec.Siv.pad P).length = 16 := by
  simp [Spec.Siv.pad, Spec.Siv.zeros]; omega

theorem length_xorend {s d : List Byte} (h : d.length ≤ s.length) :
    (Spec.Siv.xorend s d).length = s.length := by
  simp [Spec.Siv.xorend, length_xor]; omega

/-! ## CTR -/

/-- The bytes of `n` blocks of 16 bytes, concatenated. -/
theorem length_flatMap16 (g : Nat → List Byte) (hg : ∀ i, (g i).length = 16) (n : Nat) :
    ((List.range n).flatMap g).length = 16 * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hg]; omega

theorem getD_flatMap16 (g : Nat → List Byte) (hg : ∀ i, (g i).length = 16) (n : Nat) {p : Nat}
    (hp : p < 16 * n) : ((List.range n).flatMap g).getD p 0 = (g (p / 16)).getD (p % 16) 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.getD_eq_getElem?_getD]
    by_cases h : p < 16 * n
    · rw [List.getElem?_append_left (by rw [length_flatMap16 g hg]; exact h), ← List.getD_eq_getElem?_getD,
        ih h]
    · rw [List.getElem?_append_right (by rw [length_flatMap16 g hg]; omega), length_flatMap16 g hg]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [← List.getD_eq_getElem?_getD]
      have e1 : p / 16 = n := by omega
      have e2 : p % 16 = p - 16 * n := by omega
      rw [e1, e2]

/-- The keystream block of CTR from the counter `q` for block `i`. -/
abbrev ksBlock (ciph : Spec.Cmac.Cipher) (q : List Byte) (i : Nat) : List Byte :=
  ciph (Spec.Siv.be128 (Spec.Siv.beNat q + i))

theorem length_ctr (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) :
    (Spec.Siv.ctr ciph q x).length = x.length := by
  simp only [Spec.Siv.ctr, length_xor, length_flatMap16 _ (fun i => hc _)]
  omega

/-- Byte `p` of CTR's output. -/
theorem ctr_getD (ciph : Spec.Cmac.Cipher) (hc : ∀ y, (ciph y).length = 16) (q x : List Byte) {p : Nat}
    (hp : p < x.length) :
    (Spec.Siv.ctr ciph q x).getD p 0 = x.getD p 0 ^^^ (ksBlock ciph q (p / 16)).getD (p % 16) 0 := by
  have hl := length_flatMap16 (fun i => ciph (Spec.Siv.be128 (Spec.Siv.beNat q + i))) (fun i => hc _)
    ((x.length + 15) / 16)
  simp only [Spec.Siv.ctr, Spec.Siv.xor, List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem hp, List.getElem?_eq_getElem (show p < _ by rw [hl]; omega)]
  show x[p] ^^^ _ = _
  congr 1
  have h := getD_flatMap16 (fun i => ciph (Spec.Siv.be128 (Spec.Siv.beNat q + i))) (fun i => hc _)
    ((x.length + 15) / 16) (p := p) (by omega)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show p < _ by rw [hl]; omega),
    Option.getD_some] using h

end VG.Proof.Siv
