import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Finish
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.RoundLoop

namespace VG.Proof.ChaCha20.AArch64.Neon4

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (stateAt serialize block)

theorem input_eq (s : State) (k : Fin 16) (j : Nat) :
    input s k j = (ctr (stateAt s.mem (s.gpr .x0)) j)[k] := by
  simp only [input, ctr, Vector.getElem_set, stateAt, Vector.getElem_ofFn, Fin.getElem_fin]
  by_cases hk : k = 12
  · subst k; rfl
  · have hk' : k.val ≠ 12 := fun e => hk (Fin.ext e)
    simp only [hk, Ne.symm hk', ite_false]

structure ChunkKeep (s s' : State) : Prop where
  gpr : ∀ r, r ≠ .x4 → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp

theorem chunk_ok (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ r j : Fin 4, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa chunk s fun s' =>
      (∀ k < 256, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1, 256⟩] s.mem s'.mem ∧ ChunkKeep s s' := by
  apply WP.seq
  refine (setup_ok s hin).mono fun a ⟨ha, hsa, hta⟩ => ?_
  apply WP.seq
  refine (roundLoop_ok ha hta).mono fun b ⟨hb, hab⟩ => ?_
  have hsb : LoadSame s b := hsa.trans hab
  have hi : ∀ k : Fin 16, InRegions (b.rd ++ b.wr) (b.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4 := by
    intro k; rw [hsb.rd, hsb.wr, hsb.gpr _ (by decide)]; exact hin k
  apply WP.block_append
  refine (feed_ok hb hi).mono fun c ⟨hc, hbc⟩ => ?_
  have hsc := hsb.trans hbc
  have hc' : Holds (fun j => block (ctr (stateAt s.mem (s.gpr .x0)) j)) c := by
    intro k j hj
    simp only [block]
    rw [hc k j hj, input_same hsb, input_eq]
    simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  have ho : ∀ r j : Fin 4, InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j; rw [hsc.wr, hsc.gpr _ (by decide)]; exact hout r j
  refine (finishBlocks_ok hc' ho).mono fun d ⟨hd, hf, hs⟩ => ⟨?_, ?_, ?_⟩
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hd
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd, hs.wr.trans hsc.wr, hs.sp.trans hsc.sp⟩

end VG.Proof.ChaCha20.AArch64.Neon4
