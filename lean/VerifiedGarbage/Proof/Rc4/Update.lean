import VerifiedGarbage.Proof.Rc4.Stream

/-! # RC4: the stream, one byte more at a time -/

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- `update` over one more byte: the PRGA step after the context the others leave. -/
theorem update_snoc (c : Context) (xs : List Byte) (x : Byte) :
    update c (xs ++ [x]) =
      ((step (update c xs).1).1, (update c xs).2 ++ [x ^^^ (step (update c xs).1).2]) := by
  induction xs generalizing c with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.cons_append, update, ih]

theorem bytes_snoc (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p (n + 1) = bytesAt m p n ++ [m (p + BitVec.ofNat 64 n)] := by
  simp only [bytesAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- A write outside the table leaves its abstract permutation unchanged. -/
theorem table_write_sep' (m : Mem) (p q : Addr) {n : Nat} (v : BitVec (8 * n))
    (h : Mem.Sep p 256 q n) :
    (contextAt (m.write q n v) p).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  apply Mem.write_apply
  exact h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hk)

theorem bytes_frame (m m' : Mem) (d : Addr) (n : Nat)
    (h : ∀ k < n, m' (d + BitVec.ofNat 64 k) = m (d + BitVec.ofNat 64 k)) :
    bytesAt m' d n = bytesAt m d n := by
  unfold bytesAt
  apply List.map_congr_left
  intro k hk
  exact h k (List.mem_range.mp hk)

end VG.Proof.Rc4
