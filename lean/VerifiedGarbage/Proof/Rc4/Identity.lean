import VerifiedGarbage.Proof.Rc4.Memory

/-! # RC4: the identity permutation, stored a byte at a time -/

namespace VG.Proof.Rc4
open VG VG.Spec.Rc4

/-- The memory once the first `r` bytes of the table at `p` are the identity. -/
def identityMem (m : Mem) (p : Addr) (r : Nat) : Mem :=
  fun x => if (x - p).toNat < r then BitVec.ofNat 8 (x - p).toNat else m x

theorem identityMem_zero (m : Mem) (p : Addr) : identityMem m p 0 = m := by
  funext x
  simp only [identityMem, Nat.not_lt_zero, ite_false]

theorem identityMem_store (m : Mem) (p : Addr) (r : Nat) (hr : r < 256) :
    (identityMem m p r).write (p + BitVec.ofNat 64 r) 1 (BitVec.ofNat 8 r) =
      identityMem m p (r + 1) := by
  funext x
  rw [write_byte]
  have heq : x = p + BitVec.ofNat 64 r ↔ (x - p).toNat = r := by
    constructor
    · intro h; rw [h, Mem.sub_ofNat_toNat p (by omega)]
    · intro h
      have he : x - p = BitVec.ofNat 64 r := by
        apply BitVec.eq_of_toNat_eq
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rw [← he, BitVec.add_comm, BitVec.sub_add_cancel]
  simp only [identityMem, heq]
  by_cases h : (x - p).toNat = r
  · simp only [h, ite_true, Nat.lt_add_one]
  · by_cases hl : (x - p).toNat < r
    · simp only [h, hl, show (x - p).toNat < r + 1 by omega, ite_true, ite_false]
    · simp only [h, hl, show ¬ (x - p).toNat < r + 1 by omega, ite_false]

theorem identityMem_table (m : Mem) (p : Addr) :
    (contextAt (identityMem m p 256) p).table =
      Vector.ofFn (fun i : Fin 256 => BitVec.ofNat 8 i.val) := by
  apply Vector.ext
  intro k hk
  simp only [contextAt, Vector.getElem_ofFn, identityMem]
  rw [Mem.sub_ofNat_toNat p (by omega), ite_eq_left hk]

theorem identityMem_frame (m : Mem) (p : Addr) (r : Nat) (hr : r ≤ 256) :
    TableFrame p m (identityMem m p r) := by
  intro x hx
  simp only [identityMem, show ¬ (x - p).toNat < r by omega, ite_false]

/-- The key offset after `r`, advanced: back to 0 at the key length. -/
theorem key_next (r len : Nat) (hl : 0 < len) (hlen : len ≤ 256) :
    (if (BitVec.ofNat 64 (r % len) + 1#64).toNat < len then BitVec.ofNat 64 (r % len) + 1#64
      else 0#64) = BitVec.ofNat 64 ((r + 1) % len) := by
  have hb := Nat.mod_lt r hl
  have ht : (BitVec.ofNat 64 (r % len) + 1#64).toNat = r % len + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r % len < 2 ^ 64 by omega)]
    change (r % len + 1) % 2 ^ 64 = _
    omega
  rw [ht]
  have ha : (r + 1) % len = (r % len + 1) % len := by
    simp only [Nat.add_mod, Nat.mod_mod]
  by_cases h : r % len + 1 < len
  · rw [ite_eq_left h]
    apply BitVec.eq_of_toNat_eq
    rw [ht, BitVec.toNat_ofNat, ha, Nat.mod_eq_of_lt h,
      Nat.mod_eq_of_lt (show r % len + 1 < 2 ^ 64 by omega)]
  · rw [ite_eq_right h, ha, show r % len + 1 = len by omega, Nat.mod_self]

end VG.Proof.Rc4
