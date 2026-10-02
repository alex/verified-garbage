import VerifiedGarbage.Proof.Argon2.AArch64.FillKernelMappingCT
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressCT

/-! Equal permitted references give equal compression and block-update traces. -/

namespace VG.Proof.Argon2.AArch64.FillKernel

open VG VG.AArch64 VG.Spec.Argon2

theorem prepared_public {p : Params} {pass lane slice index : Nat} {s t a b : State}
    (h : Related p pass lane slice index s t)
    (ha : Prepared s a p pass lane slice index) (hb : Prepared t b p pass lane slice index) :
    FillCompress.CodeRelated a b := by
  have currentEq : current s p lane slice index = current t p lane slice index := by
    unfold current; rw [h.matrices]
  have previousEq : previous s p lane slice index = previous t p lane slice index := by
    unfold previous; rw [h.matrices]
  have referenceEq : referenced s p pass lane slice index = referenced t p pass lane slice index := by
    unfold referenced; rw [h.references, h.matrices]
  have workA : FillCompress.work a = work s := by
    unfold FillCompress.work work; rw [ha.keeps.regs .x19 (by decide), ha.keeps.mem]
  have workB : FillCompress.work b = work t := by
    unfold FillCompress.work work; rw [hb.keeps.regs .x19 (by decide), hb.keeps.mem]
  have passA : FillCompress.pass a = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [ha.keeps.regs .x19 (by decide), ha.keeps.mem]
    exact h.left.passWord
  have passB : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [hb.keeps.regs .x19 (by decide), hb.keeps.mem]
    exact h.right.passWord
  refine ⟨ha.ready, hb.ready, ?_, workA.trans (h.scratch.trans workB.symm), passA.trans passB.symm, ha.keeps.sp.trans (h.stacks.trans hb.keeps.sp.symm)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ha.previousPtr.trans (previousEq.trans hb.previousPtr.symm)
  · exact ha.referencePtr.trans (referenceEq.trans hb.referencePtr.symm)
  · exact ha.currentPtr.trans (currentEq.trans hb.currentPtr.symm)
  · exact (ha.keeps.regs .x19 (by decide)).trans (h.bases.trans (hb.keeps.regs .x19 (by decide)).symm)

theorem prepare_public_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.prepare
      FillCompress.CodeRelated := by
  have trace := (mapping_public_rel p pass lane slice index).seq (pointers_trace p lane slice index)
  have full := trace.wpDep (fun s t h =>
    ⟨prepare_ok s p pass lane slice index h.left, prepare_ok t p pass lane slice index h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  exact prepared_public hp ha hb

theorem code_rel (p : Params) (pass lane slice index : Nat) :
    RelCT isa (Related p pass lane slice index) Impl.Argon2.AArch64.FillKernel.code
      (fun s t => s.sp = t.sp) := (prepare_public_rel p pass lane slice index).seq FillCompress.code_rel

end VG.Proof.Argon2.AArch64.FillKernel
