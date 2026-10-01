import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.VectorLower
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.CoreExec

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

structure VectorFileRel (f : File) (s : VG.AArch64.State) : Prop where
  regs : ∀ r, s.gpr r = f.regs r
  slots : ∀ k < 2, vdword (s.v (slotV k)) 0 = f.slots k

private theorem slotV_eq {j k : Nat} (hj : j < 2) (hk : k < 2) :
    slotV j = slotV k ↔ j = k := by
  interval_cases j <;> interval_cases k <;> decide

private theorem slotV_ne (k : Nat) (v : VReg) (h24 : v ≠ .v24) (h25 : v ≠ .v25) :
    v ≠ slotV k := by
  unfold slotV
  split <;> assumption

/-- Every instruction realizes its abstract operation without changing memory. -/
theorem vector_step_ok (op : ScalarOp) (hg : Good op) (f : File) (s : VG.AArch64.State)
    (hr : VectorFileRel f s) :
    ∃ s', runBlock isa (lowerVector op) s = some s' ∧ VectorFileRel (step f op) s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  cases op with
  | spill k a =>
    have hk := hg.1
    refine ⟨s.setV (slotV k) (ofVDwords (s.gpr a) (s.gpr a)), ?_, ⟨?_, ?_⟩,
      rfl, rfl, rfl, rfl, ?_⟩
    · simp only [lowerVector, runBlock_cons, exec, VOp.eval, Option.map_some, runStep_some, runBlock_nil]
    · intro r; exact hr.regs r
    · intro j hj
      simp only [step, RegUpd.v_setV]
      by_cases he : j = k
      · subst j
        simp only [ite_true, vdword_ofVDwords_0, hr.regs]
      · simp only [ite_eq_right he, ite_eq_right ((slotV_eq hj hk).not.mpr he), hr.slots j hj]
    · intro v h24 h25 _ _
      exact RegUpd.v_setV_of_ne s _ (slotV_ne k v h24 h25)
  | reload d k =>
    have hk := hg.1
    refine ⟨s.write .x d (vdword (s.v (slotV k)) 0), ?_, ⟨?_, ?_⟩,
      rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
    · simp only [lowerVector, runBlock_cons, exec, Size.bits, Nat.zero_mul,
        show 0 < 128 from by decide, ite_true, runStep_some, runBlock_nil]
      rfl
    · intro r
      simp only [step, File.write, RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq, hr.slots k hk]
      split <;> simp only [hr.regs]
    · intro j hj; exact hr.slots j hj
  | _ =>
    obtain ⟨s', hs, hregs, hm, hrd, hwr, hsp, hv⟩ :=
      reg_lower_ok _ hg (by intro k r h; cases h) (by intro r k h; cases h) f s hr.regs
    refine ⟨s', hs, ⟨hregs, ?_⟩, hm, hrd, hwr, hsp, fun v _ _ _ h29 => hv v h29⟩
    · intro k hk
      rw [hv (slotV k) (by unfold slotV; split <;> decide)]
      exact hr.slots k hk

private theorem block_append (xs ys : List Instr) (s : VG.AArch64.State) :
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    change (isa.exec x s).bind (fun s' => runBlock isa (xs ++ ys) s') =
      ((isa.exec x s).bind (runBlock isa xs)).bind (runBlock isa ys)
    rw [Option.bind_assoc]
    exact congrArg (Option.bind (isa.exec x s)) (funext fun s' => ih s')

theorem vector_list_ok (ops : List ScalarOp) (hg : ∀ op ∈ ops, Good op)
    (f : File) (s : VG.AArch64.State) (hr : VectorFileRel f s) :
    ∃ s', runBlock isa (ops.flatMap lowerVector) s = some s' ∧ VectorFileRel (run ops f) s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  induction ops generalizing f s with
  | nil => exact ⟨s, rfl, hr, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl⟩
  | cons op ops ih =>
    obtain ⟨s₁, hs₁, hr₁, hm₁, hrd₁, hwr₁, hsp₁, hv₁⟩ :=
      vector_step_ok op (hg op (List.mem_cons_self ..)) f s hr
    obtain ⟨s₂, hs₂, hr₂, hm₂, hrd₂, hwr₂, hsp₂, hv₂⟩ :=
      ih (fun op ho => hg op (List.mem_cons_of_mem _ ho)) (step f op) s₁ hr₁
    refine ⟨s₂, ?_, hr₂, hm₂.trans hm₁, hrd₂.trans hrd₁, hwr₂.trans hwr₁, hsp₂.trans hsp₁,
      fun v h24 h25 h28 h29 => (hv₂ v h24 h25 h28 h29).trans (hv₁ v h24 h25 h28 h29)⟩
    simp only [List.flatMap_cons, block_append, hs₁, Option.bind_some, hs₂]

/-- The vector-slot core has the same lane semantics and writes no memory. -/
theorem vector_core_ok (A : Spec.Sha3.State) (s : VG.AArch64.State)
    (hl : ∀ i : Nat, (hi : i < 25) → s.gpr (laneReg i) = A[i]) :
    ∃ s', runBlock isa vectorCoreInstrs s = some s' ∧
      (∀ i : Nat, (hi : i < 25) → s'.gpr (laneReg i) =
        (Spec.Sha3.chi (Spec.Sha3.pi (Spec.Sha3.rho (Spec.Sha3.theta A))))[i]) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v24 → v ≠ .v25 → v ≠ .v28 → v ≠ .v29 → s'.v v = s.v v) := by
  let f : File := ⟨s.gpr, fun k => vdword (s.v (slotV k)) 0⟩
  have hr : VectorFileRel f s := ⟨fun _ => rfl, fun _ _ => rfl⟩
  have hmath := core_math A f hl
  obtain ⟨s', hs, hr', hm, hrd, hwr, hsp, hv⟩ := vector_list_ok coreOps core_good f s hr
  exact ⟨s', hs, fun i hi => (hr'.regs (laneReg i)).trans (hmath i hi), hm, hrd, hwr, hsp, hv⟩

end VG.Proof.Sha3.AArch64.Scalar
