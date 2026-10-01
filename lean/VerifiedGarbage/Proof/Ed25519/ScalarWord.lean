import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.Bytes

/-!
# Ed25519 scalar arithmetic: reduction a word at a time

Untrusted and target-independent. With `L = 2^252 + c`, a remainder `r < L`
and the next 64-bit word `w` give `v = 2^64 r + w = h 2^252 + l`; then
`l + L - h c` is below `2L` and congruent to `v` modulo `L` (`fold_nat`), so
one conditional subtraction of `L` finishes the step. The input is consumed
from its top word down (`words_step`, `mod_step`).
-/

namespace VG.Proof.Ed25519

open VG VG.Spec.Ed25519

/-- `L - 2^252`. -/
def cL : Nat := 27742317777372353535851937790883648493

theorem L_eq : L = 2 ^ 252 + cL := by decide

/-- One word folded in: `l + L - h c` is below `2L` and congruent to `v = 2^64 r + w`. -/
theorem fold_nat (r w : Nat) (hr : r < L) (hw : w < 2 ^ 64) :
    (r * 2 ^ 64 + w) / 2 ^ 252 * cL < L ∧
    (r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * cL) < 2 * L ∧
    ((r * 2 ^ 64 + w) % 2 ^ 252 + (L - (r * 2 ^ 64 + w) / 2 ^ 252 * cL)) % L =
      (r * 2 ^ 64 + w) % L := by
  rw [L_eq] at hr ⊢
  generalize hv : r * 2 ^ 64 + w = v
  have hv' : v < 2 ^ 317 := by rw [← hv]; simp only [cL] at hr; omega
  have hh : v / 2 ^ 252 < 2 ^ 65 := by omega
  have hc : v / 2 ^ 252 * cL < 2 ^ 65 * cL := Nat.mul_lt_mul_of_pos_right hh (by decide)
  have hd := Nat.div_add_mod v (2 ^ 252)
  simp only [cL] at hc ⊢
  refine ⟨by omega, by omega, ?_⟩
  generalize v / 2 ^ 252 = h at hc hd
  generalize v % 2 ^ 252 = l at hd ⊢
  subst hd
  have e : l + (2 ^ 252 + 27742317777372353535851937790883648493 -
      h * 27742317777372353535851937790883648493) +
      h * (2 ^ 252 + 27742317777372353535851937790883648493) =
      2 ^ 252 * h + l + (2 ^ 252 + 27742317777372353535851937790883648493) := by
    rw [Nat.mul_add]; omega
  rw [← Nat.add_mul_mod_self_right _ h, e, Nat.add_mod_right]

/-- A remainder taken before the next word is shifted in. -/
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

/-- The 64-byte input from word `k` up: that word, and `2^64` times the words above it. -/
theorem words_step (m : Mem) (p : Addr) (k : Nat) (hk : k < 8) :
    decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) (64 - 8 * k)) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat +
        2 ^ 64 * decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * (k + 1))) (64 - 8 * (k + 1))) := by
  have e : 64 - 8 * k = 8 + (64 - 8 * (k + 1)) := by omega
  have hs : bytesAt m (p + BitVec.ofNat 64 (8 * k)) (8 + (64 - 8 * (k + 1))) =
      bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8 ++
        bytesAt m (p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8) (64 - 8 * (k + 1)) :=
    Proof.X25519.bytesAt_add m _ 8 _
  have hw : decodeLE (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8) =
      (m.readW (p + BitVec.ofNat 64 (8 * k)) 64).toNat := by
    rw [decodeLE_eq]; exact Proof.X25519.leNum_bytesAt_64 m _
  have ha : p + BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 8 = p + BitVec.ofNat 64 (8 * (k + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * k + 8 = 8 * (k + 1) by omega]
  have hl : (bytesAt m (p + BitVec.ofNat 64 (8 * k)) 8).length = 8 := by
    simp only [bytesAt, List.length_map, List.length_range]
  rw [e, hs, decodeLE_append, hl, hw, ha]
  rfl

/-- `h₀ = r₂ >> 60 | 16 r₃`: the two parts have no bits in common. -/
theorem or_mul16 {a b : Nat} (h : a < 2 ^ 4) : a ||| 16 * b = a + 16 * b := by
  rw [show 16 * b = b * 2 ^ 4 by omega, Nat.or_comm, ← Nat.shiftLeft_eq,
    ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.add_comm]

/-- A four-word subtraction `L - T`, for `T < L`, cannot borrow. -/
theorem eq_sub_of_chain {u T c : Nat} (hu : u < 2 ^ 256) (hT : T < L)
    (e : u + T = L + 2 ^ 256 * c) : u = L - T := by
  have := order_bound
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

/-- A four-word sum below `2^256` does not carry out. -/
theorem eq_of_chain {u x c : Nat} (hx : x < 2 ^ 256) (e : u + 2 ^ 256 * c = x) : u = x := by
  rcases Nat.lt_or_ge c 1 with h | h
  · obtain rfl : c = 0 := by omega
    omega
  · have : 2 ^ 256 ≤ 2 ^ 256 * c := Nat.le_mul_of_pos_right _ h
    omega

end VG.Proof.Ed25519
