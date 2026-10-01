import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Hybrid.ChiCore

namespace VG.Proof.Sha3.AArch64.Sha3.Hybrid

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Hybrid

theorem chiInteger_ok (s : VG.AArch64.State) (a b c dest : VG.AArch64.Reg) (iota : Bool)
    (ha : a ≠ .x17) (hc : c ≠ .x17) (hd0 : dest ≠ .x0) (hd16 : dest ≠ .x16) :
    WP isa (.block (chiInteger a b c dest iota)) s fun s' =>
      Keep s s' ∧ s'.v = s.v ∧
      ∀ q, q ≠ .g .x17 → value s' q = if q = .g dest then
        chiWord (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr .x16) iota else value s q := by
  apply WP.of_runBlock
  cases iota
  all_goals
    simp (config := {decide := true}) only [chiInteger, List.cons_append, List.nil_append,
      ite_true, ite_false, runBlock_cons, runBlock_nil, exec_logic,
      State.read, isa, runStep_some, Option.some.injEq, exists_eq_left',
      RegUpd.gpr_write, ha, hc, Ne.symm hd16, Size.bits, BitVec.setWidth_eq]
    refine ⟨?_, ?_, ?_⟩
    · constructor <;> simp (config := {decide := true}) only [RegUpd.gpr_write,
        Ne.symm hd0, Ne.symm hd16, ite_false, RegUpd.mem_write,
        RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write]
    · simp only [RegUpd.v_write]
    · intro q hq
      simp only [value_write, hq, ite_false, chiWord, Bool.false_eq_true, ite_true,
        VG.Proof.Sha3.AArch64.andNot] <;> split <;> rfl

end VG.Proof.Sha3.AArch64.Sha3.Hybrid
