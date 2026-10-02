import VerifiedGarbage.Proof.Argon2.AArch64.DeriveStore

/-! Normalize the four register-passed u32 parameters. -/
namespace VG.Proof.Argon2.AArch64.Derive
open VG VG.AArch64

structure Entered (s t : State) : Prop where
  values : ∀ r ∈ [Reg.x0, .x5, .x6, .x7], t.gpr r = ((s.gpr r).setWidth 32).setWidth 64
  regs : ∀ r, r ∉ [Reg.x0, .x5, .x6, .x7] → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem entry_ok (s : State) :
    WP isa (.block (([.x0, .x5, .x6, .x7] : List Reg).flatMap
      (fun r => Impl.Argon2.AArch64.Instructions.mov32 r r))) s (Entered s) := by
  apply WP.of_runBlock
  simp only [List.flatMap_cons, List.flatMap_nil, Impl.Argon2.AArch64.Instructions.mov32,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, BitVec.or_self, RegUpd.gpr_write,
    reduceCtorEq, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
end VG.Proof.Argon2.AArch64.Derive
