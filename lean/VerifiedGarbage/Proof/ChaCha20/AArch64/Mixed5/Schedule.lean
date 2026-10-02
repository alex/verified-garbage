import VerifiedGarbage.Impl.ChaCha20.AArch64.Mixed5
import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon4.Rounds
import VerifiedGarbage.Proof.ChaCha20.AArch64.Block

/-! Interleaving independent integer and vector operations preserves both streams. -/
namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
namespace Scheduled
open VG.Impl.ChaCha20.AArch64.Neon4 (Op)
open VG.Proof.ChaCha20.AArch64.Neon4 (step)
abbrev N := VG.Proof.ChaCha20.AArch64.Neon4.Holds
abbrev C := VG.Proof.ChaCha20.AArch64.Holds
abbrev RI := VG.Proof.ChaCha20.AArch64.RI
abbrev wreg := VG.Impl.ChaCha20.AArch64.wreg

def Valid : Op → Prop
  | .add .. => True
  | .xorRol _ _ _ n => 0 < n.val

theorem wreg_eq (a b : Fin 16) : wreg a = wreg b ↔ a = b := by
  constructor
  · intro h
    exact Fin.ext (VG.Proof.ChaCha20.AArch64.wreg_inj a.isLt b.isLt h)
  · intro h; rw [h]

theorem scalar_op (op : Op) (hv : Valid op) {v : CState} {s : State} (h : C v s) :
    WP isa (.block (scalarCode op)) s fun u => RI (step v op) s u ∧ u.v = s.v ∧ u.sp = s.sp := by
  have hh (k : Fin 16) : s.read .w (wreg k) = v[k] := by
    simp (config := {decide := true}) only [State.read, Size.bits, h k.val k.isLt, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Fin.getElem_fin]
  have keep (r : Reg) (hr : ¬ VG.Proof.ChaCha20.AArch64.Words r) (d : Fin 16) : r ≠ wreg d := by
    intro e; exact hr ⟨d.val,d.isLt,e⟩
  cases op with
  | add d a b =>
    apply WP.of_runBlock
    simp only [scalarCode, runBlock_cons, runBlock_nil, exec_add, isa, runStep_some,
      Option.some.injEq, exists_eq_left', hh]
    refine ⟨⟨?_,rfl,rfl,rfl,?_⟩,rfl,rfl⟩
    · intro k hk
      have he := wreg_eq (⟨k,hk⟩ : Fin 16) d
      simp only [State.write, Size.bits, step, Vector.getElem_set, he, Fin.ext_iff, eq_comm]
      split
      · rfl
      · exact h k hk
    · intro r hr
      simp [State.write, keep r hr d]
  | xorRol d a b n =>
    have hn : 32 - n.val < 32 := by change 0 < n.val at hv; omega
    apply WP.of_runBlock
    simp (config := {decide := true}) only [scalarCode, runBlock_cons, runBlock_nil, exec_logic, exec_ror_w hn, isa,
      runStep_some, Option.some.injEq, exists_eq_left',
      State.read, State.write, Size.bits, h a.val a.isLt, h b.val b.isLt,
      ite_true, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    refine ⟨⟨?_,rfl,rfl,rfl,?_⟩, trivial⟩
    · intro k hk
      have he := wreg_eq (⟨k,hk⟩ : Fin 16) d
      simp only [step, Vector.getElem_set, he, Fin.ext_iff, eq_comm]
      split
      · simp only [VG.Proof.ChaCha20.rotateLeft_eq _ hv n.isLt, Fin.getElem_fin]
      · exact h k hk
    · intro r hr
      simp [keep r hr d]

theorem ops_ok (ops : List Op) (hp : ∀ op ∈ ops, Valid op)
    {vs : Nat → CState} {v : CState} {s : State}
    (hn : N vs s) (ht : s.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table) (hc : C v s) :
    WP isa (scheduled ops) s fun u =>
      N (fun j => ops.foldl step (vs j)) u ∧ RI (ops.foldl step v) s u ∧ u.sp = s.sp ∧
      u.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by
  induction ops generalizing vs v s with
  | nil => exact WP.block_nil ⟨hn,⟨hc,rfl,rfl,rfl,fun _ _ => rfl⟩,rfl,ht⟩
  | cons op ops ih =>
    apply WP.seq
    refine (VG.Proof.ChaCha20.AArch64.Neon4.op_ok op hn ht).mono fun a ⟨ha,hsa⟩ => ?_
    have hca : C v a := by simpa only [C, VG.Proof.ChaCha20.AArch64.Holds,hsa.gpr] using hc
    apply WP.seq
    refine (scalar_op op (hp _ (List.mem_cons_self ..)) hca).mono fun b ⟨hb,hav,hsp⟩ => ?_
    have hnb : N (fun j => step (vs j) op) b := by
      simpa only [N, VG.Proof.ChaCha20.AArch64.Neon4.Holds,hav] using ha
    have htb : b.v .v30 = VG.Impl.ChaCha20.AArch64.Neon4.rol8Table := by rw [hav,hsa.v30,ht]
    refine (ih (fun p h => hp p (List.mem_cons_of_mem _ h)) hnb htb hb.holds).mono
      fun u ⟨hu,hbu,hsp',hut⟩ => ?_
    refine ⟨hu,?_,hsp'.trans (hsp.trans hsa.sp),hut⟩
    refine ⟨hbu.holds,hbu.mem.trans (hb.mem.trans hsa.mem),
        hbu.rd.trans (hb.rd.trans hsa.rd),hbu.wr.trans (hb.wr.trans hsa.wr),?_⟩
    intro r hr
    exact (hbu.keep r hr).trans ((hb.keep r hr).trans (congrFun hsa.gpr r))

theorem roundOps_valid : ∀ op ∈ roundOps, Valid op := by
  have h : roundOps.all (fun op => match op with
    | .add .. => true | .xorRol _ _ _ n => decide (0 < n.val)) = true := by decide +kernel
  intro op hp
  have hh := List.all_eq_true.mp h op hp
  cases op
  · trivial
  · change 0 < _
    exact of_decide_eq_true hh
end Scheduled
end VG.Proof.ChaCha20.AArch64.Mixed5
