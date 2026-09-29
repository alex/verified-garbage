import VerifiedGarbage.Proof.Framework.Mem

/-!
# Writing a list of bytes

Untrusted: everything here is checked by Lean. `writeBytes m q xs` is `m`
with the bytes `xs` written from `q` on, for the streaming proofs of the
hash functions (which export these names into their own namespaces).
-/

namespace VG.WriteBytes

/-- `m` with the bytes `xs` written from `q` on. -/
def writeBytes (m : Mem) (q : Addr) (xs : List Byte) : Mem :=
  fun a => if (a - q).toNat < xs.length then xs.getD (a - q).toNat 0 else m a

theorem writeBytes_nil (m : Mem) (q : Addr) : writeBytes m q [] = m := by
  funext a; simp [writeBytes]

theorem writeW8_apply (m : Mem) (a x : Addr) (b : Byte) :
    m.writeW a b x = if x = a then b else m x := by
  simp only [Mem.writeW, Mem.write]
  by_cases h : x = a
  · subst h; simp
  · have : ¬ (x - a).toNat < 8 / 8 := by
      intro h'
      apply h
      have : (x - a).toNat = 0 := by omega
      have : x - a = 0 := BitVec.eq_of_toNat_eq (by simpa using this)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add a
    simp only [this, h, ite_false]

theorem writeBytes_snoc (m : Mem) (q : Addr) (xs : List Byte) (b : Byte) (h : xs.length < 2 ^ 64) :
    writeBytes m q (xs ++ [b]) = (writeBytes m q xs).writeW (q + BitVec.ofNat 64 xs.length) b := by
  funext a
  rw [writeW8_apply]
  simp only [writeBytes, List.length_append, List.length_singleton]
  by_cases ha : a = q + BitVec.ofNat 64 xs.length
  · subst ha
    rw [Offset.add_sub_cancel_left,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
    simp [List.getD_eq_getElem?_getD]
  · have hne : (a - q).toNat ≠ xs.length := by
      intro h'
      apply ha
      have : a - q = BitVec.ofNat 64 xs.length := BitVec.eq_of_toNat_eq (by rw [h', BitVec.toNat_ofNat, Nat.mod_eq_of_lt h])
      rw [← BitVec.sub_add_cancel a q, this, BitVec.add_comm]
    simp only [ha, ite_false]
    by_cases hl : (a - q).toNat < xs.length
    · simp only [show (a - q).toNat < xs.length + 1 by omega, hl, ite_true]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hl]
    · simp only [show ¬ (a - q).toNat < xs.length + 1 by omega, hl, ite_false]

/-- The bytes before `q` (within `2⁶⁴ - |xs|`) are unchanged. -/
theorem writeBytes_before (m : Mem) (q : Addr) (xs : List Byte) {i d : Nat} (hi : i < d)
    (h : d + xs.length < 2 ^ 64) :
    writeBytes m (q + BitVec.ofNat 64 d) xs (q + BitVec.ofNat 64 i) = m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes]
  split
  · rename_i hc
    rw [show q + BitVec.ofNat 64 i - (q + BitVec.ofNat 64 d) = BitVec.ofNat 64 i - BitVec.ofNat 64 d by
      rw [← BitVec.sub_sub, BitVec.add_comm q, BitVec.add_sub_cancel], BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (a := d) (by omega), show 2 ^ 64 - d + i = 2 ^ 64 - (d - i) by omega,
      Nat.mod_eq_of_lt (by omega)] at hc
    omega
  · rfl

theorem writeBytes_frame (m : Mem) (q : Addr) (xs : List Byte) {R : Region} (hR : R.Contains q xs.length) :
    Frame [R] m (writeBytes m q xs) := by
  intro x hx
  simp only [writeBytes]
  split
  · rename_i h; exact absurd (hR.byte h) (hx R (List.mem_singleton_self _))
  · rfl

/-- A little-endian write is a write of its bytes. -/
theorem write_eq_writeBytes (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) :
    m.write a n v = writeBytes m a ((List.range n).map fun j => v.extractLsb' (8 * j) 8) := by
  funext x
  simp only [Mem.write, writeBytes, List.length_map, List.length_range]
  split
  · rename_i h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h, Option.map_some,
      Option.getD_some]
  · rfl

/-- Writing `ys` right after `xs`. -/
theorem writeBytes_append (m : Mem) (q : Addr) (xs ys : List Byte) (h : xs.length + ys.length < 2 ^ 64) :
    writeBytes (writeBytes m q xs) (q + BitVec.ofNat 64 xs.length) ys = writeBytes m q (xs ++ ys) := by
  funext a
  simp only [writeBytes, List.length_append]
  have hq : (a - (q + BitVec.ofNat 64 xs.length)).toNat =
      ((a - q).toNat + (18446744073709551616 - xs.length)) % 18446744073709551616 := by
    rw [show a - (q + BitVec.ofNat 64 xs.length) = (a - q) - BitVec.ofNat 64 xs.length from
        (BitVec.sub_sub _ _ _).symm,
      BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := xs.length) (by omega),
      Nat.add_comm]
  have hlt : (a - q).toNat < 18446744073709551616 := (a - q).isLt
  have h' : xs.length + ys.length < 18446744073709551616 := h
  by_cases h1 : (a - q).toNat < xs.length
  · have ht : ¬ (a - (q + BitVec.ofNat 64 xs.length)).toNat < ys.length := by rw [hq]; omega
    simp only [ht, h1, ite_false, ite_true, show (a - q).toNat < xs.length + ys.length by omega]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · have ht : (a - (q + BitVec.ofNat 64 xs.length)).toNat = (a - q).toNat - xs.length := by rw [hq]; omega
    simp only [ht, h1, ite_false]
    by_cases h2 : (a - q).toNat < xs.length + ys.length
    · simp only [show (a - q).toNat - xs.length < ys.length by omega, h2, ite_true]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : xs.length ≤ (a - q).toNat)]
    · simp only [show ¬ (a - q).toNat - xs.length < ys.length by omega, h2, ite_false]

end VG.WriteBytes
