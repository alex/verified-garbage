import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.Framework.X86_64.Bswap

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.Spec.TripleDes

theorem decodeBlock_readW (m : Mem) (p : Addr) :
    decodeBlock (blockAt m p) = bswap64 (m.readW p 64) := by
  rw [VG.Proof.TripleDes.decodeBlock_cat, bswap64_readW]
  simp only [VG.Proof.TripleDes.catBlock, blockAt, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.add_zero]
  rfl

end VG.Proof.TripleDes.X86_64
