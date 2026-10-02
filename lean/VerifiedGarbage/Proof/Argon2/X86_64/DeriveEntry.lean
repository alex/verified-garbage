import VerifiedGarbage.Proof.Argon2.X86_64.DeriveStore

/-! Establish the local frame base and normalize register-passed u32 arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure Entered (s t : State) : Prop where
  bp : t.gpr .rbp = s.gpr .rsp
  kind : t.gpr .rdi = ((s.gpr .rdi).setWidth 32).setWidth 64
  passes : t.gpr .r9 = ((s.gpr .r9).setWidth 32).setWidth 64
  regs : ∀ r, r ≠ .rbp → r ≠ .rdi → r ≠ .r9 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  mxcsr : t.mxcsr = s.mxcsr

theorem entry_ok (s : State) :
    WP isa (.block [.mov .rbp (.reg .rsp), .mov32 .rdi (.reg .rdi), .mov32 .r9 (.reg .r9)]) s (Entered s) := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, RegUpd.gpr_setReg, reduceCtorEq,
    ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  intro r hb hd h9
  simp only [RegUpd.gpr_setReg, hb, hd, h9, ite_false]

end VG.Proof.Argon2.X86_64.Derive
