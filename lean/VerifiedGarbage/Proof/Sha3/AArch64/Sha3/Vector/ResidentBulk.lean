import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLoop
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
open VG.Spec.Sha3 (stateAt)

structure FinishedAt (b : State) (consumed : Nat) (s : State) : Prop where
  c_le : consumed ≤ len b
  aligned : consumed % rate b = 0
  x3 : s.gpr .x3 = data b + BitVec.ofNat 64 consumed
  x4 : s.gpr .x4 = BitVec.ofNat 64 (len b-consumed)
  vcs : ∀ r ∈ VG.AArch64.preservedV, (s.v r).extractLsb' 0 64 = (b.v r).extractLsb' 0 64
  repr : ∀ msg, stateAt b.mem (st b) = VG.Proof.Sha3.Rep (rate b) msg → msg.length % rate b = 0 →
    stateAt s.mem (st b) = VG.Proof.Sha3.Rep (rate b) (msg ++ Spec.Sha3.bytesAt b.mem (data b) consumed)

def Finished (b s : State) : Prop := ∃ c, FinishedAt b c s

theorem finish_ok (b : State) (hp : BulkPre b) (s₀ : State) (hs : Setup b s₀)
    (c : Nat) (A : Spec.Sha3.State) (s : State) (h : LoopState b s₀.mem c A s)
    (h0 : s.gpr .x0 = b.gpr .x0) (h1 : s.gpr .x1 = b.gpr .x1) :
    WP isa (.block (store ++ restore)) s (Finished b) := by
  rw [WP.block_append_iff]
  have hout : ∀ i < 12, InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 (16*i)) 16 := by
    intro i hi
    rw [h.wr,hp.wr,h0]
    exact ⟨stateR b,by simp,state_pair_contains b hi⟩
  have hlast : InRegions s.wr (VG.Proof.Sha3.laneAddr (s.gpr .x0) 24) 8 := by
    rw [h.wr,hp.wr,h0]
    exact ⟨stateR b,by simp,VG.Proof.Sha3.lane_contains _ (by decide : 24<25)⟩
  refine (WP.gprs (store_ok s A h.lanes hout hlast) (rs := [.x3,.x4])
    (by decide +kernel) rfl).mono fun t ⟨⟨hp',hf,ha⟩,hg⟩ => ?_
  have saved : Saved b t.mem := by
    intro i hi
    rw [hf.read (scratch_contains b hi) ?_ (by decide),h.mem]
    · exact hs.saved i hi
    · intro r hr
      have he := List.mem_singleton.mp hr
      subst r
      rw [h0]
      exact (hp.st_scr.sub_right (Region.sub_prefix (by decide))).symm
  refine (restore_ok b t saved (hp'.x1.trans h1) (fun i hi => ?_)).mono fun u ⟨hk,hv⟩ => ?_
  · rw [hp'.rd,hp'.wr,h.rd,h.wr,hp.rd,hp.wr,hp'.x1,h1]
    exact ⟨scratchR b,by simp,Offset.contains_base _ (by change 16*i+16 ≤ 640; omega) (by omega)⟩
  · refine ⟨c,⟨h.c_le,h.aligned,?_,?_,hv,?_⟩⟩
    · exact (congrFun hk.gpr .x3).trans ((hg .x3 (by simp)).trans h.x3)
    · exact (congrFun hk.gpr .x4).trans ((hg .x4 (by simp)).trans h.x4)
    · intro msg hm hal
      rw [hk.mem]
      rw [h0] at ha
      exact ha.trans (h.repr msg hm hal)

theorem functional (b : State) (hp : BulkPre b) : WP isa bulk b (Finished b) := by
  unfold bulk
  apply WP.seq
  refine (setup_ok b hp).mono fun s₀ hs => ?_
  apply WP.seq
  have loop := VG.AArch64.WP.gprs (loop_ok b hp s₀ hs) (rs := [.x0,.x1]) ?_ rfl
  · exact loop.mono fun s ⟨⟨c,A,h⟩,hg⟩ => finish_ok b hp s₀ hs c A s h
      ((hg .x0 (by simp)).trans (hs.gpr .x0 (by simp)))
      ((hg .x1 (by simp)).trans (hs.gpr .x1 (by simp)))
  · change body.allInstrs (fun i => [.x0,.x1].all fun r => dstOf i != some r) = true
    lit_decide

theorem bulk_correct (b : State) (hp : BulkPre b) : WP isa bulk b (BulkPost b) := by
  have hc : bulk.allInstrs (fun i => (VG.AArch64.preserved ++ [Reg.x0,Reg.x1,Reg.x2,Reg.x5,Reg.x6]).all
      fun r => dstOf i != some r) = true := by lit_decide
  obtain ⟨t,s,he,⟨c,hf⟩,hg⟩ := VG.AArch64.WP.gprs (functional b hp) hc (by lit_decide)
  have hh := Exec.regions he (by lit_decide)
  refine ⟨t,s,he,c,⟨hf.c_le,hf.aligned,⟨fun r hr => hg r (by simp [hr]),hh.2.2.1,hf.vcs⟩,
    hh.1,hh.2.1,?_,hg .x0 (by simp),hg .x1 (by simp),hg .x2 (by simp),hf.x3,hf.x4,
    hg .x5 (by simp),hg .x6 (by simp),hf.repr⟩⟩
  simpa only [hp.wr] using hh.2.2.2

#assert_standard_axioms bulk_correct

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
