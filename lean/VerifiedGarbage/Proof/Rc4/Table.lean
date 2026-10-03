import VerifiedGarbage.Spec.Rc4

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

theorem context_ext {a b : Context} (ht : a.table = b.table) (hi : a.i = b.i)
    (hj : a.j = b.j) : a = b := by
  cases a
  cases b
  cases ht
  cases hi
  cases hj
  rfl

theorem get_byte (s : Table) (idx : Byte) : s.getD idx.toNat 0 = s[idx.toNat]'idx.isLt := by
  simp [Vector.getD, Array.getD, idx.isLt]

/-- Read a swapped table, including the case where both indices coincide. -/
theorem swap_get (s : Table) (i j k : Byte) :
    (swap s i j).getD k.toNat 0 =
      if k = j then s.getD i.toNat 0 else if k = i then s.getD j.toNat 0 else s.getD k.toNat 0 := by
  simp only [get_byte, swap, Vector.getElem_set! k.isLt]
  have hij (a b : Byte) : a.toNat = b.toNat ↔ a = b := BitVec.toNat_inj
  simp only [hij, eq_comm]

theorem swap_self (s : Table) (i : Byte) : swap s i i = s := by
  apply Vector.ext
  intro k hk
  simp only [swap, get_byte, Vector.getElem_set! hk]
  by_cases h : i.toNat = k
  · subst k; simp
  · simp only [h, ite_false]

theorem swap_i (s : Table) (i j : Byte) :
    (swap s i j).getD i.toNat 0 = s.getD j.toNat 0 := by
  rw [swap_get]
  by_cases h : i = j
  · subst j; simp
  · simp only [h, ite_false, ite_true]

theorem swap_j (s : Table) (i j : Byte) :
    (swap s i j).getD j.toNat 0 = s.getD i.toNat 0 := by
  rw [swap_get, ite_eq_left rfl]

/-- Swapping leaves the sum of the two selected bytes unchanged. -/
theorem swap_sum (s : Table) (i j : Byte) :
    (swap s i j).getD i.toNat 0 + (swap s i j).getD j.toNat 0 =
      s.getD i.toNat 0 + s.getD j.toNat 0 := by
  rw [swap_i, swap_j, BitVec.add_comm]

/-- The output lookup index can use the two original selected bytes. -/
theorem step_eq (ctx : Context) :
    step ctx =
      let i := ctx.i + 1
      let a := ctx.table.getD i.toNat 0
      let j := ctx.j + a
      let b := ctx.table.getD j.toNat 0
      let s := swap ctx.table i j
      ({ table := s, i, j }, s.getD (a + b).toNat 0) := by
  dsimp only [step]
  rw [swap_sum]

end VG.Proof.Rc4
