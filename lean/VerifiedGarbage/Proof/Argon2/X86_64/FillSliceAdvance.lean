import VerifiedGarbage.Impl.Argon2.X86_64.FillSlices
import VerifiedGarbage.Proof.Argon2.X86_64.FillSlice

/-! Slice advancement retains the public header and matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillSlices

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.FillSlices

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    t.gpr .r14 = s.gpr .r14 + 1 ∧ t.cf = decide ((s.gpr .r14 + 1).toNat < 4) ∧ Divide.Keeps [.r14] s t := by
  apply WP.of_runBlock
  simp only [advance, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags,
    show BitVec.signExtend 64 (1 : BitVec 32) = (1 : Addr) from rfl,
    show BitVec.signExtend 64 (4 : BitVec 32) = (4 : Addr) from rfl,
    show (4 : Addr).toNat = 4 from rfl,
    ite_true, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  all_goals rfl

theorem advanced_header {s t : State} {p : Params} {pass lane slice : Nat}
    (h : FillHeader.Ready p pass lane slice s) (k : Divide.Keeps [.r14] s t)
    (value : t.gpr .r14 = BitVec.ofNat 64 (slice + 1)) : FillHeader.Ready p pass lane (slice + 1) t := by
  obtain ⟨old, words⟩ := h.words
  exact h.of_state (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide))
    k.mem k.rd k.wr ((k.regs .rbx (by decide)).trans words.laneWord) value

end VG.Proof.Argon2.X86_64.FillSlices
