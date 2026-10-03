import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Spec.ChaCha20 (stateAt serialize block)
abbrev ChunkKeep := VG.Proof.ChaCha20.AArch64.Neon4.ChunkKeep

theorem chunk_ok (s : State)
    (hin : ∀ k : Fin 24, InRegions (s.rd ++ s.wr)
      (s.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16)
    (hctr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + 48) 4)
    (hout : ∀ k : Fin 24, InRegions s.wr (s.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16) :
    WP isa chunk s fun u =>
      (∀ k < 384, u.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1,384⟩] s.mem u.mem ∧ ChunkKeep s u := by
  apply WP.seq
  refine (setup_ok s hin hctr).mono fun a ⟨ha,hsa,hta⟩ => ?_
  apply WP.seq
  refine (rounds_ok ha hta 10).mono fun b ⟨hb,hab⟩ => ?_
  have hsb : LoadSame s b := hsa.trans
    ⟨fun r _ => congrFun hab.gpr r,hab.mem,hab.rd,hab.wr,hab.sp⟩
  have hi : ∀ k : Fin 24, InRegions (b.rd ++ b.wr)
      (b.gpr .x0 + BitVec.ofNat 64 (16 * (k.val % 4))) 16 := by
    intro k; rw [hsb.rd,hsb.wr,hsb.gpr _ (by decide)]; exact hin k
  have hc : InRegions (b.rd ++ b.wr) (b.gpr .x0 + 48) 4 := by
    rw [hsb.rd,hsb.wr,hsb.gpr _ (by decide)]; exact hctr
  apply WP.block_append
  refine (feedForward_ok b hi hc).mono fun c ⟨hfeed,hbc⟩ => ?_
  have hsc := hsb.trans hbc
  have hblocks : Holds (pack (fun j => block (ctr (stateAt s.mem (s.gpr .x0)) j))) c := by
    intro k j hj
    rw [hfeed k j hj,hb k j hj,input_same hsb,input_ctr s k j hj]
    simp only [pack_get,block,Vector.getElem_zipWith]
  have ho : ∀ k : Fin 24, InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (16 * k.val)) 16 := by
    intro k; rw [hsc.wr,hsc.gpr _ (by decide)]; exact hout k
  refine (finishBlocks_ok hblocks ho).mono fun u ⟨hu,hf,hs⟩ => ⟨?_,?_,?_⟩
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4),hsc.mem] using hu
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4),hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd,hs.wr.trans hsc.wr,hs.sp.trans hsc.sp⟩
end VG.Proof.ChaCha20.AArch64.Rows6
