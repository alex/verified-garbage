import VerifiedGarbage.Spec.Ed448.Contract
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# Ed448 scalar arithmetic: the numbers

`L = 2^446 - c` with `c < 2^224`. Folding a word into a remainder below `L`
(`fold_nat`) leaves a value below `2L` and congruent to it; a conditional
subtraction (`csub_nat`) then leaves the remainder. The bytes of the
specification are X25519's little-endian numbers (`decodeLE_eq`).
-/

namespace VG.Proof.Ed448

open VG VG.Spec.Ed448

/-- `c = 2^446 - L`. -/
def cL : Nat := 13818066809895115352007386748515426880336692474882178609894547503885

theorem L_add : L + cL = 2 ^ 446 := by decide +kernel
theorem cL_lt : cL < 2 ^ 224 := by decide +kernel
theorem L_pos : 0 < L := by decide +kernel
theorem L_lt : L < 2 ^ 446 := by decide +kernel
theorem K_eq : 2 ^ 448 - L = 3 * 2 ^ 446 + cL := by decide +kernel

theorem L_lit : L = 181709681073901722637330951972001133588410340171829515070372549795146003961539585716195755291692375963310293709091662304773755859649779 := by
  decide +kernel

/-- One word folded in, on words (exponents above 256 stay unevaluated, so
the numbers are written with nested factors `2^64`): the remainder
`r = (r₀, …, r₆) < L` and the next word `w` give `v = w + 2^64 r =
h 2^446 + l`, with `l = (w, r₀, …, r₄, r₅ mod 2^62)` and
`h = r₅ / 2^62 + 4 r₆`; then `l + h c` is below `2L` and congruent to `v`
modulo `L`. -/
theorem fold_words (w r0 r1 r2 r3 r4 r5 r6 : Nat) (hw : w < 2 ^ 64) (h0 : r0 < 2 ^ 64)
    (h1 : r1 < 2 ^ 64) (h2 : r2 < 2 ^ 64) (h3 : r3 < 2 ^ 64) (h4 : r4 < 2 ^ 64)
    (h5 : r5 < 2 ^ 64) (h6 : r6 < 2 ^ 64)
    (hr : r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 * (r4 + 2 ^ 64 *
      (r5 + 2 ^ 64 * r6))))) < L) :
    let l := w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 *
      (r4 + 2 ^ 64 * (r5 % 2 ^ 62))))))
    let h := r5 / 2 ^ 62 + 4 * r6
    r6 < 2 ^ 62 ∧ h < 2 ^ 64 ∧ l + h * cL < 2 * L ∧
      (l + h * cL) % L = (w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 +
        2 ^ 64 * (r4 + 2 ^ 64 * (r5 + 2 ^ 64 * r6))))))) % L := by
  intro l h
  have hL := L_lit
  have hc : cL = 13818066809895115352007386748515426880336692474882178609894547503885 := rfl
  have h6' : r6 < 2 ^ 62 := by rw [hL] at hr; omega
  have hh : h < 2 ^ 64 := by omega
  have hhc : h * cL < 2 ^ 64 * 2 ^ 224 := Nat.mul_lt_mul'' hh (by rw [hc]; omega)
  have e : w + 2 ^ 64 * (r0 + 2 ^ 64 * (r1 + 2 ^ 64 * (r2 + 2 ^ 64 * (r3 + 2 ^ 64 * (r4 +
      2 ^ 64 * (r5 + 2 ^ 64 * r6)))))) = (l + h * cL) + L * h := by
    rw [hL, hc]; omega
  refine ⟨h6', hh, by rw [hL] at *; omega, ?_⟩
  rw [e, Nat.add_mul_mod_self_left]

/-- The conditional subtraction: `K = M - L` added to `x < 2L` carries out of
`M` (`2^448`) exactly when `x ≥ L`, and then the sum is `x - L`. -/
theorem csub_nat {M x y : Nat} {c : Bool} (hM : 2 * L ≤ M) (hx : x < 2 * L) (hy : y < M)
    (he : y + M * c.toNat = x + (M - L)) :
    (if c then y else x) = x % L := by
  have hL := L_pos
  cases c with
  | false =>
    simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at he
    rw [ite_eq_right Bool.false_ne_true, Nat.mod_eq_of_lt (by omega)]
  | true =>
    simp only [Bool.toNat_true, Nat.mul_one] at he
    rw [ite_eq_left rfl, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- Folding a word into the remainder of the words above it. -/
theorem mod_step (a w : Nat) : (a % L * 2 ^ 64 + w) % L = (w + 2 ^ 64 * a) % L := by
  have hd := Nat.mod_add_div a L
  generalize a % L = r at hd ⊢
  generalize a / L = q at hd
  subst hd
  rw [← Nat.add_mul_mod_self_left (r * 2 ^ 64 + w) L (q * 2 ^ 64)]
  congr 1
  rw [Nat.mul_add, Nat.add_comm w, Nat.add_assoc, Nat.add_comm w, ← Nat.add_assoc,
    Nat.mul_comm (2 ^ 64) r, Nat.mul_left_comm (2 ^ 64) L q, Nat.mul_comm (2 ^ 64) q,
    ← Nat.mul_assoc]

theorem decodeLE_eq (xs : List Byte) : decodeLE xs = Proof.X25519.leNum xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [decodeLE, Proof.X25519.leNum, ih]

theorem decodeLE_append (xs ys : List Byte) :
    decodeLE (xs ++ ys) = decodeLE xs + 256 ^ xs.length * decodeLE ys := by
  simp only [decodeLE_eq, Proof.X25519.leNum_append]

theorem decodeLE_lt' (xs : List Byte) : decodeLE xs < 256 ^ xs.length := by
  rw [decodeLE_eq]; exact Proof.X25519.leNum_lt xs

theorem encodeLE_eq (n x : Nat) : encodeLE n x = Proof.X25519.leBytes n x := by
  simp only [encodeLE, Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem bytesAt_eq (m : Mem) (p : Addr) (n : Nat) : bytesAt m p n = Spec.X25519.bytesAt m p n := rfl

theorem leBytes_one (x : Nat) : Proof.X25519.leBytes 1 x = [BitVec.ofNat 8 x] := by
  simp [Proof.X25519.leBytes]

/-- A point's encoding (§5.2.2): the 56 bytes of `y < 2^448`, then the sign
bit `b` as the top bit of the 57th byte. Stated here, where `2 ^ 455` is the
specification's term. -/
theorem encodeLE_57 (y b : Nat) (hy : y < 256 ^ 56) :
    encodeLE 57 (y + b * 2 ^ 455) =
      Proof.X25519.leBytes 56 y ++ [BitVec.ofNat 8 (128 * b)] := by
  have h455 : (2 : Nat) ^ 455 = 256 ^ 56 * 128 := by decide +kernel
  rw [encodeLE_eq, show 57 = 56 + 1 from rfl, Proof.X25519.leBytes_add, h455, leBytes_one]
  generalize hM : (256 : Nat) ^ 56 = M at *
  have hM0 : 0 < M := by omega
  have e1 : (y + b * (M * 128)) % M = y := by
    rw [show y + b * (M * 128) = y + M * (b * 128) by grind, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy]
  have e2 : (y + b * (M * 128)) / M = 128 * b := by
    rw [show y + b * (M * 128) = y + M * (b * 128) by grind, Nat.add_mul_div_left _ _ hM0, Nat.div_eq_of_lt hy,
      Nat.zero_add, Nat.mul_comm]
  rw [e2, ← Proof.X25519.leBytes_mod 56, hM, e1]

end VG.Proof.Ed448
