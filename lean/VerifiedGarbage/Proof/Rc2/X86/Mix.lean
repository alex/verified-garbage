import VerifiedGarbage.Proof.Rc2.X86.Words

/-! # RC2 MIX arithmetic, including its inverse -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.RegUpd VG.Impl.Rc2.X86

theorem mask16_ok (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .and r (.imm 65535)] s = some s' ∧
      s'.gpr r = ((s.gpr r).setWidth 16).setWidth 32 ∧ Keep [r] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, exec, execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil]
    rfl, ?_⟩
  constructor
  · rw [gpr_setReg_self]; exact Word32.maskWord _
  · exact ⟨fun r' hr => (gpr_setReg_of_ne _ _ (by simpa using hr)), rfl, rfl, rfl⟩

theorem argAddr_keep {s s' : State} {rs : List Reg} (h : Keep rs s s')
    (sp : .esp ∉ rs) (i : Nat) : argAddr s' i = argAddr s i := by
  unfold argAddr; rw [h.reg .esp sp]

def mixValue (sub : Bool) (x c k : BitVec 32) : BitVec 16 :=
  (if sub then x - c - k else x + c + k).setWidth 16

theorem mixArithmetic_ok (sub : Bool) (s : State) (i j : Nat) (hj : j < 64)
    (stackRead : InRegions (s.rd ++ s.wr) (argAddr s 0) 4)
    (fit : (arg s 0).toNat + 128 ≤ 2 ^ 32)
    (readable : ∀ n < 128, InRegions (s.rd ++ s.wr) (addr32 (arg s 0) + BitVec.ofNat 64 n) 1) :
    WP isa (.block (mixArithmetic sub j i)) s (fun s' =>
      s'.gpr (wordReg i) = (mixValue sub (s.gpr (wordReg i))
        ((s.gpr (wordReg (i + 3)) &&& s.gpr (wordReg (i + 2))) +
          (~~~(s.gpr (wordReg (i + 3))) &&& s.gpr (wordReg (i + 1))))
        (((Spec.Rc2.scheduleAt s.mem (addr32 (arg s 0))).getD j 0).setWidth 32)).setWidth 32 ∧
      Keep (wordReg i :: temps) s s') := by
  rw [mixArithmetic, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, out₁, keep₁⟩ := mixSelect_ok s i
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₂, run₂, out₂, keep₂⟩ := adjust_ok sub s₁ (wordReg i)
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [WP.block_append_iff]
  have k₁ : Keep (wordReg i :: temps) s s₁ := keep₁.weaken (by simp [temps])
  have k₂ : Keep (wordReg i :: temps) s₁ s₂ := keep₂.weaken (by simp)
  have keep := k₁.trans k₂
  have sp : .esp ∉ wordReg i :: temps := by
    simp only [List.mem_cons, temps, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm (wordReg_separate i).2.2.2, by decide, by decide⟩
  have args := arg_keep keep sp 0
  have stack := argAddr_keep keep sp 0
  obtain ⟨s₃, run₃, out₃, keep₃⟩ := mixKey_ok s₂ j hj
    (by rw [keep.rd, keep.wr, stack]; exact stackRead)
    (by rw [args]; exact fit)
    (by rw [keep.rd, keep.wr, args]; exact readable)
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  rw [WP.block_append_iff]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := adjust_ok sub s₃ (wordReg i)
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  obtain ⟨s₅, run₅, out₅, keep₅⟩ := mask16_ok s₄ (wordReg i)
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  constructor
  · rw [out₅, out₄, keep₃.reg _ (wordReg_not_temps i), out₂,
      keep₁.reg _ (by simp only [List.mem_singleton]; exact (wordReg_separate i).1),
      out₁, out₃, keep.mem, args]
    cases sub <;> simp only [mixValue, Bool.false_eq_true, ite_true, ite_false]
  · exact ((keep.trans (keep₃.weaken (by simp [temps]))).trans
      (keep₄.weaken (by simp))).trans (keep₅.weaken (by simp))

theorem mixValue_add (x k a b c : BitVec 16) :
    mixValue false (x.setWidth 32)
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))
      (k.setWidth 32) = x + k + (a &&& b) + (~~~a &&& c) := by
  simp only [mixValue, Bool.false_eq_true, ite_false, BitVec.setWidth_add _ _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_and, BitVec.setWidth_not (show 16 ≤ 32 by decide), BitVec.setWidth_setWidth_of_le _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_eq]
  ac_rfl

theorem mixValue_sub (x k a b c : BitVec 16) :
    mixValue true (x.setWidth 32)
      ((a.setWidth 32 &&& b.setWidth 32) + (~~~(a.setWidth 32) &&& c.setWidth 32))
      (k.setWidth 32) = x - k - (a &&& b) - (~~~a &&& c) := by
  simp only [mixValue, ite_true, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ (show 16 ≤ 32 by decide),
    BitVec.setWidth_neg_of_le (show 16 ≤ 32 by decide), BitVec.setWidth_and, BitVec.setWidth_not (show 16 ≤ 32 by decide),
    BitVec.setWidth_setWidth_of_le _ (show 16 ≤ 32 by decide), BitVec.setWidth_eq]
  simp only [BitVec.neg_add, BitVec.sub_eq_add_neg]
  ac_rfl

end VG.Proof.Rc2.X86
