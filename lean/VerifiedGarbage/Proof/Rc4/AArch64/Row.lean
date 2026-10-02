import VerifiedGarbage.Proof.Rc4.AArch64.Select
import VerifiedGarbage.Proof.Rc4.Memory

/-! A fixed-address row store changes only the selected secret byte. -/
namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Proof.Rc4

/-- Replace within a row using the low byte of `idx - off`. The table has
256 bytes, and every row is aligned to a 16-byte offset within it. -/
theorem write_row (m : Mem) (p : Addr) (idx value : Byte) (r : Nat) (hr : r < 16) :
    m.write (p + BitVec.ofNat 64 (16 * r)) 16
      (replaceVector (m.read (p + BitVec.ofNat 64 (16 * r)) 16)
        (idx - BitVec.ofNat 8 (16 * r)) value) =
    if 16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1) then
      m.write (p + BitVec.ofNat 64 idx.toNat) 1 value else m := by
  let row := p + BitVec.ofNat 64 (16 * r)
  let target := p + BitVec.ofNat 64 idx.toNat
  let rowIdx := idx - BitVec.ofNat 8 (16 * r)
  have htest : rowIdx.toNat < 16 ↔ 16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1) := by
    dsimp [rowIdx]; bv_omega
  funext x
  by_cases hrow : (x - row).toNat < 16
  · change (if (x - row).toNat < 16 then
        vbyte (replaceVector (m.read row 16) rowIdx value) (x - row).toNat else m x) = _
    rw [ite_eq_left hrow, replace_lane _ _ _ _ hrow]
    have hread : vbyte (m.read row 16) (x - row).toNat = m x := by
      unfold vbyte
      rw [Mem.extractLsb'_read _ _ hrow, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
    rw [hread]
    by_cases hhit : 16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1)
    · rw [ite_eq_left hhit, write_byte]
      have hsame : rowIdx.toNat = (x - row).toNat ↔ x = target := by
        dsimp [row, target, rowIdx]; bv_omega
      simp only [hsame]
      rfl
    · rw [ite_eq_right hhit, ite_eq_right (show ¬rowIdx.toNat = (x - row).toNat by
        intro he; exact hhit (htest.mp (he ▸ hrow)))]
  · change (if (x - row).toNat < 16 then _ else m x) = _
    rw [ite_eq_right hrow]
    by_cases hhit : 16 * r ≤ idx.toNat ∧ idx.toNat < 16 * (r + 1)
    · rw [ite_eq_left hhit, write_byte, ite_eq_right (show x ≠ target by
        intro he; subst x; apply hrow; dsimp [target, row]; bv_omega)]
    · rw [ite_eq_right hhit]

end VG.Proof.Rc4.AArch64
