import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed8
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Schedule

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Spec.ChaCha20 (innerBlock)
abbrev Rows := VG.Proof.ChaCha20.AArch64.Rows6.Rows
abbrev N := VG.Proof.ChaCha20.AArch64.Rows6.Holds
abbrev C := VG.Proof.ChaCha20.AArch64.Holds
abbrev RI := VG.Proof.ChaCha20.AArch64.RI
abbrev VS := (Nat → Rows) × CState

variable {sve : Bool}

def step (v : VS) : Op → VS
  | .vector op => (VG.Proof.ChaCha20.AArch64.Rows6.step v.1 op,v.2)
  | .scalar op => (v.1,VG.Proof.ChaCha20.AArch64.Neon4.step v.2 op)

def Valid : Op → Prop
  | .vector _ => True
  | .scalar op => VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.Valid op

theorem op_ok (op : Op) (hp : Valid op) {v : VS} {s : State}
    (hn : N v.1 s) (hc : C v.2 s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (.block (op.code sve)) s fun u =>
      N (step v op).1 u ∧ RI (step v op).2 s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  cases op with
  | vector op =>
    refine (VG.Proof.ChaCha20.AArch64.Rows6.op_ok_for sve op hn ht).mono fun u ⟨hu,hs⟩ => ?_
    have hcu : C v.2 u := by simpa only [C,VG.Proof.ChaCha20.AArch64.Holds,hs.gpr] using hc
    exact ⟨hu,⟨hcu,hs.mem,hs.rd,hs.wr,fun r _ => congrFun hs.gpr r⟩,hs.sp,hs.v30.trans ht⟩
  | scalar op =>
    refine (VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.scalar_op op hp hc).mono
      fun u ⟨hu,hv,hsp⟩ => ?_
    have hnu : N v.1 u := by simpa only [N,VG.Proof.ChaCha20.AArch64.Rows6.Holds,hv] using hn
    exact ⟨hnu,hu,hsp,by rw [hv]; exact ht⟩

theorem ops_ok (ops : List Op) (hp : ∀ op ∈ ops, Valid op) {v : VS} {s : State}
    (hn : N v.1 s) (hc : C v.2 s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (scheduled sve ops) s fun u =>
      N (ops.foldl step v).1 u ∧ RI (ops.foldl step v).2 s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  induction ops generalizing v s with
  | nil => exact WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | cons op ops ih =>
    apply WP.seq
    refine (op_ok op (hp _ (List.mem_cons_self ..)) hn hc ht).mono fun a ⟨ha,hr,hsp,hat⟩ => ?_
    refine (ih (fun p h => hp p (List.mem_cons_of_mem _ h)) ha hr.holds hat).mono
      fun u ⟨hu,hau,hsp',hut⟩ => ?_
    exact ⟨hu,⟨hau.holds,hau.mem.trans hr.mem,hau.rd.trans hr.rd,hau.wr.trans hr.wr,
      fun r hr' => (hau.keep r hr').trans (hr.keep r hr')⟩,hsp'.trans hsp,hut⟩

theorem scalar_fold (ss : List VG.Impl.ChaCha20.AArch64.Neon4.Op) (v : VS) :
    ((ss.map Op.scalar).foldl step v) =
      (v.1,ss.foldl VG.Proof.ChaCha20.AArch64.Neon4.step v.2) := by
  induction ss generalizing v with
  | nil => rfl
  | cons op ss ih => simpa only [List.map_cons,List.foldl_cons,step] using ih (step v (.scalar op))

theorem interleave_fold (vs : List VG.Impl.ChaCha20.AArch64.Rows6.Op)
    (ss : List VG.Impl.ChaCha20.AArch64.Neon4.Op) (v : VS) :
    (interleave vs ss).foldl step v =
      (vs.foldl VG.Proof.ChaCha20.AArch64.Rows6.step v.1,
        ss.foldl VG.Proof.ChaCha20.AArch64.Neon4.step v.2) := by
  induction vs generalizing ss v with
  | nil => exact scalar_fold ss v
  | cons op vs ih =>
    cases ss with
    | nil => simpa only [interleave,List.foldl_cons,List.foldl_nil,step] using ih [] (step v (.vector op))
    | cons p ss =>
      simpa only [interleave,List.foldl_cons,step] using ih ss (step (step v (.vector op)) (.scalar p))

theorem interleave_valid (vs : List VG.Impl.ChaCha20.AArch64.Rows6.Op)
    (ss : List VG.Impl.ChaCha20.AArch64.Neon4.Op)
    (hp : ∀ op ∈ ss, VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.Valid op) :
    ∀ op ∈ interleave vs ss, Valid op := by
  induction vs generalizing ss with
  | nil =>
    intro op h
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp h
    exact hp p hp'
  | cons p vs ih =>
    cases ss with
    | nil =>
      intro op h
      simp only [interleave,List.mem_cons] at h
      rcases h with rfl | h
      · trivial
      · exact ih [] hp op h
    | cons q ss =>
      intro op h
      simp only [interleave,List.mem_cons] at h
      rcases h with rfl | rfl | h
      · trivial
      · exact hp q (List.mem_cons_self ..)
      · exact ih ss (fun q h => hp q (List.mem_cons_of_mem _ h)) op h

theorem parallelRound_ok {blocks : Nat → CState} {v : CState} {s : State}
    (hn : N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (parallelRound sve) s fun u =>
      N (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun b => innerBlock (blocks b))) u ∧
      RI (innerBlock (innerBlock v)) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  have hv : ∀ op ∈ roundOps, Valid op := interleave_valid _ _ (by
    intro op h
    rcases List.mem_append.mp h with h | h <;>
      exact VG.Proof.ChaCha20.AArch64.Mixed5.Scheduled.roundOps_valid op h)
  refine (ops_ok roundOps hv (v := (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks,v)) hn hc ht).mono
    fun u ⟨hu,hr,hsp,hut⟩ => ?_
  have hf := interleave_fold VG.Impl.ChaCha20.AArch64.Rows6.roundOps
    (VG.Impl.ChaCha20.AArch64.Mixed5.roundOps ++ VG.Impl.ChaCha20.AArch64.Mixed5.roundOps)
    (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks,v)
  change roundOps.foldl step (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks,v) = _ at hf
  rw [hf] at hu hr
  have hs : (VG.Impl.ChaCha20.AArch64.Mixed5.roundOps ++
      VG.Impl.ChaCha20.AArch64.Mixed5.roundOps).foldl
      VG.Proof.ChaCha20.AArch64.Neon4.step v = innerBlock (innerBlock v) := by
    rw [List.foldl_append]
    simp only [VG.Impl.ChaCha20.AArch64.Mixed5.roundOps,
      VG.Proof.ChaCha20.AArch64.Neon4.innerBlock_eq]
  change RI ((VG.Impl.ChaCha20.AArch64.Mixed5.roundOps ++
      VG.Impl.ChaCha20.AArch64.Mixed5.roundOps).foldl
      VG.Proof.ChaCha20.AArch64.Neon4.step v) s u at hr
  rw [hs] at hr
  refine ⟨?_,hr,hsp,hut⟩
  intro k j hj
  exact (hu k j hj).trans (VG.Proof.ChaCha20.AArch64.Rows6.round_eq blocks k j hj)

theorem rounds_ok {blocks : Nat → CState} {v : CState} {s : State}
    (hn : N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    ∀ n, WP isa (rounds sve n) s fun u =>
      N (VG.Proof.ChaCha20.AArch64.Rows6.pack
        (fun b => Nat.repeat innerBlock n (blocks b))) u ∧
      RI (Nat.repeat (fun x => innerBlock (innerBlock x)) n v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table
  | 0 => WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | n + 1 => by
    apply WP.seq
    refine (rounds_ok hn hc ht n).mono fun a ⟨ha,hra,hspa,hat⟩ => ?_
    refine (parallelRound_ok ha hra.holds hat).mono fun u ⟨hu,hru,hspu,hut⟩ => ?_
    exact ⟨hu,⟨hru.holds,hru.mem.trans hra.mem,hru.rd.trans hra.rd,hru.wr.trans hra.wr,
      fun r hr => (hru.keep r hr).trans (hra.keep r hr)⟩,hspu.trans hspa,hut⟩

theorem phase_ok {blocks : Nat → CState} {v : CState} {s : State}
    (hn : N (VG.Proof.ChaCha20.AArch64.Rows6.pack blocks) s) (hc : C v s)
    (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) :
    WP isa (rounds sve 5) s fun u =>
      N (VG.Proof.ChaCha20.AArch64.Rows6.pack
        (fun b => Nat.repeat innerBlock 5 (blocks b))) u ∧
      RI (Nat.repeat innerBlock 10 v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  have he (f : CState → CState) (x : CState) :
      Nat.repeat (fun x => f (f x)) 5 x = Nat.repeat f 10 x := rfl
  refine (rounds_ok hn hc ht 5).mono fun u ⟨hu,hr,hsp,hut⟩ => ?_
  rw [he innerBlock v] at hr
  exact ⟨hu,hr,hsp,hut⟩

end VG.Proof.ChaCha20.AArch64.Mixed8
