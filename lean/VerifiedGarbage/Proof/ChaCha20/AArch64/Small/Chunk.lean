import VerifiedGarbage.Impl.ChaCha20.AArch64.Small
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Chunk

namespace VG.Proof.ChaCha20.AArch64.Small
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Small
open VG.Proof.ChaCha20.AArch64.Neon4
open VG.Spec.ChaCha20 (stateAt serialize block)

def selected (n : Nat) : List Nat :=
  (List.finRange 4).flatMap (fun r => (lanes n).map (slot r))

theorem selected_mem (n : Nat) (hn : n ≤ 4) (k : Nat) (hk : k < 16) :
    k ∈ selected n ↔ k < 4*n :=
  (show ∀ n < 5, ∀ k < 16, k ∈ selected n ↔ k < 4*n by decide) n (by omega) k hk

theorem finish_ok {n : Nat} (hn : n ≤ 4) {s : State} {vs : Nat → CState} (h : VG.Proof.ChaCha20.AArch64.Neon4.Holds vs s)
    (hout : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64*j+16*r)) 16) :
    WP isa (.block ((List.finRange 4).flatMap (VG.Impl.ChaCha20.AArch64.Neon4.finishRowFor (lanes n)))) s fun s' =>
      (∀ k < 64*n, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^ (serialize (vs (k/64))).getD (k%64) 0) ∧
      Frame [⟨s.gpr .x1, 64*n⟩] s.mem s'.mem ∧ Keep s s' := by
  have hj : (lanes n).Nodup := (List.nodup_finRange 4).sublist (List.filter_sublist)
  refine (finishRowsFor_ok (lanes n) hj (List.finRange 4) (List.nodup_finRange 4)
    (Data.nil s.mem (s.gpr .x1) (output vs)) rfl (fun r _ i j => h (VG.Impl.ChaCha20.AArch64.Neon4.rowWord r i) j j.isLt)
    (fun _ _ _ _ => List.not_mem_nil) hout).mono fun u ⟨hd,hs⟩ => ⟨?_,?_,hs⟩
  · intro k hk
    have hk256 : k < 256 := by omega
    rw [hd _, Mem.sub_ofNat_toNat _ (by omega : k < 2^64),
      ite_eq_left ⟨List.mem_append_left _ ((selected_mem n hn (k/16) (by omega)).mpr (by omega)),hk256⟩,
      output_byte vs hk256]
  · intro x hx
    have hnot : ¬ (x-s.gpr .x1).toNat < 64*n := by
      have h := hx ⟨s.gpr .x1,64*n⟩ (List.mem_cons_self ..)
      simp only [Region.Contains] at h
      omega
    rw [hd x, ite_eq_right]
    intro hh
    have hmem : (x-s.gpr .x1).toNat/16 ∈ selected n := by simpa only [selected, List.append_nil] using hh.1
    have := (selected_mem n hn ((x-s.gpr .x1).toNat/16) (by omega)).mp hmem
    omega

theorem chunk_ok (n : Nat) (hn : n ≤ 4) (s : State)
    (hin : ∀ k : Fin 16, InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4)
    (hout : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions s.wr
      (s.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16) :
    WP isa (chunk n) s fun s' =>
      (∀ k < 64*n, s'.mem (s.gpr .x1 + BitVec.ofNat 64 k) =
        s.mem (s.gpr .x1 + BitVec.ofNat 64 k) ^^^
        (serialize (block (ctr (stateAt s.mem (s.gpr .x0)) (k / 64)))).getD (k % 64) 0) ∧
      Frame [⟨s.gpr .x1, 64*n⟩] s.mem s'.mem ∧ ChunkKeep s s' := by
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
  have hc' : VG.Proof.ChaCha20.AArch64.Neon4.Holds (fun j => block (ctr (stateAt s.mem (s.gpr .x0)) j)) c := by
    intro k j hj
    simp only [block]
    rw [hc k j hj, input_same hsb, input_eq]
    simp only [Fin.getElem_fin, Vector.getElem_zipWith]
  have ho : ∀ r : Fin 4, ∀ j ∈ lanes n, InRegions c.wr (c.gpr .x1 + BitVec.ofNat 64 (64 * j + 16 * r)) 16 := by
    intro r j hj; rw [hsc.wr, hsc.gpr _ (by decide)]; exact hout r j hj
  refine (finish_ok hn hc' ho).mono fun d ⟨hd, hf, hs⟩ => ⟨?_, ?_, ?_⟩
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hd
  · simpa only [hsc.gpr _ (by decide : Reg.x1 ≠ .x4), hsc.mem] using hf
  · exact ⟨fun r hr => by rw [hs.gpr]; exact hsc.gpr r hr,
      hs.rd.trans hsc.rd, hs.wr.trans hsc.wr, hs.sp.trans hsc.sp⟩

end VG.Proof.ChaCha20.AArch64.Small
