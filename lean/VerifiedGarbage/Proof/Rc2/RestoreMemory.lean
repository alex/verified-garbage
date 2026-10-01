import VerifiedGarbage.Proof.Framework.Mem

/-! # Restoring a temporary vector store exactly -/

namespace VG.Proof.Rc2

theorem restore128 (m : VG.Mem) (p : VG.Addr) (v : BitVec 128) :
    (m.writeW p v).writeW p (m.readW p 128) = m := by
  funext q
  by_cases h : (q - p).toNat < 16
  · simp only [VG.Mem.writeW, VG.Mem.write, BitVec.setWidth_eq, h, ite_true,
      VG.Mem.readW]
    rw [VG.Mem.extractLsb'_read m p h]
    have he : p + BitVec.ofNat 64 (q - p).toNat = q := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm p, BitVec.sub_add_cancel]
    rw [he]
  · simp only [VG.Mem.writeW, VG.Mem.write, h, ite_false]

end VG.Proof.Rc2
