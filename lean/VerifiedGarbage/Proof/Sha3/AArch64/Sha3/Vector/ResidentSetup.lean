import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentBoundary
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Permute

namespace VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Spec.Sha3 (stateAt bytesAt)

structure Setup (b s : State) : Prop where
  gpr : ∀ r ∈ [.x0,.x1,.x3,.x4,.x6], s.gpr r = b.gpr r
  rd : s.rd = b.rd
  wr : s.wr = b.wr
  sp : s.sp = b.sp
  frame : Frame [stateR b,scratchR b] b.mem s.mem
  saved : Saved b s.mem
  lanes : Lanes s (stateAt b.mem (st b))

theorem save_gpr : ∀ r, ∀ i ∈ save, dstOf i ≠ some r := by intro r; cases r <;> decide +kernel

theorem bulk_save (b : State) (hp : BulkPre b) :
    WP isa (.block save) b fun s =>
      (∀ r, s.gpr r = b.gpr r) ∧ s.rd = b.rd ∧ s.wr = b.wr ∧ s.sp = b.sp ∧
      Frame [stateR b,scratchR b] b.mem s.mem ∧ Saved b s.mem ∧
      stateAt s.mem (st b) = stateAt b.mem (st b) := by
  let q := b.withRegions [] [stateR b,⟨scratch b,512⟩]
  have hpq : VG.Proof.Sha3.AArch64.Pre q :=
    ⟨rfl,rfl,hp.st_scr.sub_right (Region.sub_prefix (by decide))⟩
  obtain ⟨t,s,he,hptr,hv,hf,hs⟩ := save_ok q hpq
  have hw : Covers q.wr b.wr := by
    rw [hp.wr]
    apply Covers.of_sub
    intro r hr
    change r ∈ [stateR b,⟨scratch b,512⟩] at hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨stateR b,by simp,0,by simp,by simp⟩
    · exact ⟨scratchR b,by simp,0,by simp,by change 512 ≤ 640; decide⟩
  have hc : Covers (q.rd ++ q.wr) (b.rd ++ b.wr) := by
    change Covers q.wr (b.rd ++ b.wr)
    intro p n hi
    obtain ⟨r,hr,hc⟩ := hw p n hi
    exact ⟨r,List.mem_append_right _ hr,hc⟩
  have he' := Exec.widen he hc hw
  simp only [q,State.withRegions_withRegions,State.withRegions_self] at he'
  have hh := Exec.regions he' (by rfl)
  refine ⟨t,s.withRegions b.rd b.wr,he',fun r => Exec.gpr (c := .block save) (r := r) (save_gpr r) he' (.inl rfl),
    rfl,rfl,hh.2.2.1,?_,hs,?_⟩
  · simpa only [hp.wr] using hh.2.2.2
  · have h := state_frame q s hpq hptr.x0 hf
    simpa only [q,State.withRegions_gpr,State.withRegions_mem,hptr.x0] using h

theorem setup_ok (b : State) (hp : BulkPre b) :
    WP isa (.block (save ++ load)) b (Setup b) := by
  rw [WP.block_append_iff]
  refine (bulk_save b hp).mono fun s ⟨hg,hr,hw,hsp,hf,hs,ha⟩ => ?_
  have hl := WP.gprs (load_ok s (fun i hi => ?_) ?_)
    (rs := [.x0,.x1,.x3,.x4,.x6])
    (by decide +kernel) rfl
  · refine hl.mono fun s' ⟨⟨hptr,hm,hA⟩,hreg⟩ => ?_
    refine ⟨fun r hr => (hreg r hr).trans (hg r),hptr.rd.trans hr,hptr.wr.trans hw,hptr.sp.trans hsp,?_,?_,?_⟩
    · rwa [hm]
    · rwa [hm]
    · rw [hg .x0,ha] at hA
      exact hA
  · rw [hr,hw,hp.rd,hp.wr,hg .x0]
    exact ⟨stateR b,by simp,state_pair_contains b hi⟩
  · rw [hr,hw,hp.rd,hp.wr,hg .x0]
    exact ⟨stateR b,by simp,VG.Proof.Sha3.lane_contains _ (by decide : 24 < 25)⟩

end VG.Proof.Sha3.AArch64.Sha3.Vector.Resident
