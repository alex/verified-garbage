import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X448.Invert

/-!
# X448: the ladder one iteration at a time

Untrusted: everything here is checked by Lean. `X448` of the spec folds
`ladderStep` over the bits `447, …, 0` of the scalar; implementations loop
over them with a counter. `ladderAfter k x1 n` is the ladder's state after
the iterations for the bits `447` down to `n` (so `ladderAfter k x1 448` is
the initial state and `ladderAfter k x1 0` the final one), and each
iteration takes it from `n + 1` to `n` (`ladderAfter_step`). `x448_eq`
states the spec with it, and with the inversion as `invert`.
-/

namespace VG.Proof.X448

open VG.Spec.X448

/-- The ladder's initial state, for `x_1 = u`. -/
def init (u : Fe) : Ladder := { x2 := 1, z2 := 0, x3 := u, z3 := 1, swap := 0 }

/-- The ladder's state after the iterations for the bits `447` down to `n`. -/
def ladderAfter (k : Nat) (x1 : Fe) (n : Nat) : Ladder :=
  ((List.range 448).reverse.take (448 - n)).foldl (ladderStep k x1) (init x1)

theorem ladderAfter_448 (k : Nat) (x1 : Fe) : ladderAfter k x1 448 = init x1 := rfl

theorem take_reverse_range {n : Nat} (hn : n < 448) :
    (List.range 448).reverse.take (448 - n) = (List.range 448).reverse.take (448 - (n + 1)) ++ [n] := by
  rw [show 448 - n = 448 - (n + 1) + 1 by omega, List.take_add_one]
  congr
  rw [List.getElem?_reverse (by simp; omega), List.getElem?_range (by simp; omega)]
  simp only [List.length_range, Option.toList_some, List.cons.injEq, and_true]
  omega

theorem ladderAfter_step (k : Nat) (x1 : Fe) {n : Nat} (hn : n < 448) :
    ladderAfter k x1 n = ladderStep k x1 (ladderAfter k x1 (n + 1)) n := by
  rw [ladderAfter, take_reverse_range hn, List.foldl_append]
  rfl

theorem ladderAfter_zero (k : Nat) (x1 : Fe) :
    ladderAfter k x1 0 = (List.range 448).reverse.foldl (ladderStep k x1) (init x1) := by
  rw [ladderAfter, Nat.sub_zero, List.take_of_length_le (by simp)]

/-- `k_t`, the bit `t` of the scalar. -/
def bit (k t : Nat) : Nat := (k >>> t) &&& 1

theorem bit_le (k t : Nat) : bit k t ≤ 1 := by
  simp only [bit]; exact Nat.le_of_lt_succ (Nat.and_lt_two_pow _ (by decide : 1 < 2 ^ 1))

theorem ladderAfter_swap_le (k : Nat) (x1 : Fe) {n : Nat} (hn : n ≤ 448) :
    (ladderAfter k x1 n).swap ≤ 1 := by
  rcases Nat.lt_or_ge n 448 with h | h
  · rw [ladderAfter_step k x1 h]; exact bit_le k n
  · rw [show n = 448 by omega]; exact Nat.zero_le _

/-- One iteration, spelled out: the new `swap` and the swaps by it, then the
formulas. -/
theorem ladderStep_eq (k : Nat) (x1 : Fe) (st : Ladder) (t : Nat) :
    ladderStep k x1 st t =
      let s := st.swap ^^^ bit k t
      let x2 := (cswap s st.x2 st.x3).1
      let x3 := (cswap s st.x2 st.x3).2
      let z2 := (cswap s st.z2 st.z3).1
      let z3 := (cswap s st.z2 st.z3).2
      let A := x2 + z2
      let AA := A * A
      let B := x2 - z2
      let BB := B * B
      let E := AA - BB
      let C := x3 + z3
      let D := x3 - z3
      let DA := D * A
      let CB := C * B
      { x2 := AA * BB, z2 := E * (AA + a24 * E), x3 := (DA + CB) * (DA + CB),
        z3 := x1 * ((DA - CB) * (DA - CB)), swap := bit k t } := rfl

/-- `X448` with the ladder's final state and `invert`. -/
theorem x448_eq (kb ub : List Byte) :
    x448 kb ub =
      let k := decodeScalar448 kb
      let st := ladderAfter k (toFe (decodeUCoordinate ub)) 0
      encodeUCoordinate ((cswap st.swap st.x2 st.x3).1 * invert (cswap st.swap st.z2 st.z3).1) := by
  simp only [invert_eq, ladderAfter_zero]
  rfl

end VG.Proof.X448
