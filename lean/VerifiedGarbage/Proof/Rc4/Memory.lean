import VerifiedGarbage.Proof.Rc4.Table
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

theorem write_byte (m : Mem) (p x : Addr) (value : Byte) :
    m.write p 1 value x = if x = p then value else m x := by
  unfold Mem.write
  by_cases h : x = p
  · subst x
    simp only [BitVec.sub_self, show (0#64).toNat = 0 from rfl, Nat.zero_lt_succ,
      ite_true, Nat.mul_zero]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp [hk]
  · have hne : ¬(x - p).toNat < 1 := by bv_omega
    simp only [hne, h, ite_false]

/-- A vector store whose bytes equal the old memory is a memory identity. -/
theorem write_read (m : Mem) (p : Addr) (n : Nat) : m.write p n (m.read p n) = m := by
  funext x
  unfold Mem.write
  by_cases h : (x - p).toNat < n
  · rw [ite_eq_left h, Mem.extractLsb'_read _ _ h]
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
  · rw [ite_eq_right h]

theorem table_get (m : Mem) (p : Addr) (idx : Byte) :
    (contextAt m p).table.getD idx.toNat 0 = m (p + BitVec.ofNat 64 idx.toNat) := by
  rw [get_byte]
  simp only [contextAt, Vector.getElem_ofFn]

theorem table_write (m : Mem) (p : Addr) (idx value : Byte) :
    (contextAt (m.write (p + BitVec.ofNat 64 idx.toNat) 1 value) p).table =
      (contextAt m p).table.set! idx.toNat value := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn, Vector.getElem_set! hk, write_byte]
  have heq : p + BitVec.ofNat 64 k = p + BitVec.ofNat 64 idx.toNat ↔ idx.toNat = k := by
    rw [BitVec.add_right_inj]
    constructor
    · intro h
      have hn := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show idx.toNat < 2 ^ 64 by omega)] at hn
      exact hn.symm
    · intro h; rw [h]
  simp only [heq]

theorem table_swap (m : Mem) (p : Addr) (i j : Byte) :
    (contextAt ((m.write (p + BitVec.ofNat 64 j.toNat) 1
      (m (p + BitVec.ofNat 64 i.toNat))).write (p + BitVec.ofNat 64 i.toNat) 1
        (m (p + BitVec.ofNat 64 j.toNat))) p).table = swap (contextAt m p).table i j := by
  rw [table_write, table_write]
  unfold swap
  rw [table_get, table_get]
  apply Vector.ext
  intro k hk
  simp only [Vector.getElem_set! hk]
  by_cases hj : j.toNat = k
  · subst k
    by_cases hi : i.toNat = j.toNat
    · rw [hi]
    · simp only [hi, ite_true, ite_false]
  · by_cases hi : i.toNat = k
    · simp only [hi, hj, ite_true, ite_false]
    · simp only [hi, hj, ite_false]

/-- A write outside the table leaves its abstract permutation unchanged. -/
theorem table_write_sep (m : Mem) (p q : Addr) (value : Byte)
    (h : Mem.Sep p 256 q 1) :
    (contextAt (m.write q 1 value) p).table = (contextAt m p).table := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn]
  apply Mem.write_apply
  exact h _ (by rw [Mem.sub_ofNat_toNat p (by omega)]; exact hk)

/-- Scheduling modifies only the 256-byte table. -/
def TableFrame (p : Addr) (m m' : Mem) : Prop :=
  ∀ x, ¬ (x - p).toNat < 256 → m' x = m x

theorem TableFrame.refl (p : Addr) (m : Mem) : TableFrame p m m := fun _ _ => rfl

theorem TableFrame.trans {p : Addr} {a b c : Mem} (h : TableFrame p a b)
    (k : TableFrame p b c) : TableFrame p a c := fun x hx => (k x hx).trans (h x hx)

theorem swap_frame (m : Mem) (p : Addr) (i j : Byte) :
    TableFrame p m ((m.write (p + BitVec.ofNat 64 j.toNat) 1
      (m (p + BitVec.ofNat 64 i.toNat))).write (p + BitVec.ofNat 64 i.toNat) 1
        (m (p + BitVec.ofNat 64 j.toNat))) := by
  intro x hx
  have hne (idx : Byte) : x ≠ p + BitVec.ofNat 64 idx.toNat := by
    intro he
    apply hx
    rw [he, Mem.sub_ofNat_toNat p (by omega)]
    exact idx.isLt
  rw [write_byte, ite_eq_right (hne _), write_byte, ite_eq_right (hne _)]

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem bytes_get (m : Mem) (p : Addr) (n k : Nat) (hk : k < n) :
    (bytesAt m p n).getD k 0 = m (p + BitVec.ofNat 64 k) := by
  simp [bytesAt, List.getD, hk]

/-- Any bounded offset access inside an already valid region is valid. -/
theorem region_offset (rs : List Region) (p : Addr) (n d k : Nat)
    (hd : d < 2 ^ 64) (hk : d + k ≤ n) (hp : InRegions rs p n) :
    InRegions rs (p + BitVec.ofNat 64 d) k := by
  obtain ⟨region, hregion, hcontains⟩ := hp
  refine ⟨region, hregion, ?_⟩
  unfold Region.Contains at hcontains ⊢
  rw [Offset.add_sub_comm, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]
  have hmod := Nat.mod_le ((p - region.base).toNat + d) (2 ^ 64)
  omega

/-- Writing the two stream indices completes the abstract context. -/
theorem context_finish (m : Mem) (p : Addr) (i j : Byte) :
    contextAt ((m.write (p + 256#64) 1 i).write (p + 257#64) 1 j) p =
      { table := (contextAt m p).table, i, j } := by
  apply context_ext
  · rw [table_write_sep, table_write_sep]
    · exact Offset.sep_base p (by decide) (by decide)
    · exact Offset.sep_base p (by decide) (by decide)
  · change ((m.write (p + 256#64) 1 i).write (p + 257#64) 1 j) (p + 256#64) = i
    rw [write_byte, ite_eq_right (show p + 256#64 ≠ p + 257#64 by bv_omega),
      write_byte, ite_eq_left rfl]
  · change ((m.write (p + 256#64) 1 i).write (p + 257#64) 1 j) (p + 257#64) = j
    rw [write_byte, ite_eq_left rfl]

end VG.Proof.Rc4
