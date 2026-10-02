import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Contract

/-! # Streaming RC2-CBC on x86-64: the straight-line blocks -/

set_option linter.unusedSimpArgs false
namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

/-- `test r, r`: ZF is set iff `r` is 0. -/
theorem test_ok (s : State) (r : Reg) {n : Nat} (hn : s.gpr r = BitVec.ofNat 64 n) (hn' : n < 2 ^ 64) :
    ∃ s', runBlock isa [.alu .test r (.reg r)] s = some s' ∧ s'.zf = some (decide (n = 0)) ∧ Keep [] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, Option.bind_some]
    rfl, ?_⟩
  refine ⟨?_, ⟨fun r _ => by rw [gpr_arithFlags], rfl, rfl, rfl⟩⟩
  rw [zf_arithFlags, hn, BitVec.and_self, beq_zero hn']

theorem shortArgs_ok (s : State) :
    ∃ s', runBlock isa [rr .rax .rdi, .alu .add .rax (.reg .rsi)] s = some s' ∧
      s'.gpr .rax = s.gpr .rdi + s.gpr .rsi ∧ Keep [.rax] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, Option.map_some, gpr_setReg_self, gpr_setReg_of_ne]
    rfl, ?_⟩
  refine ⟨by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  have hr : r ≠ .rax := by simpa using hr
  rw [gpr_setReg_of_ne _ _ hr, gpr_arithFlags, gpr_setReg_of_ne _ _ hr]

theorem toOut_ok (s : State) :
    ∃ s', runBlock isa toOut s = some s' ∧
      s'.gpr .r9 = s.gpr .r9 - s.gpr .rsi ∧ s'.gpr .r8 = s.gpr .r8 + s.gpr .rsi ∧ Keep [.r9, .r8] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [toOut, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags, gpr_setReg_of_ne _ _ hr.1]

theorem toPending_ok (s : State) :
    ∃ s', runBlock isa toPending s = some s' ∧
      s'.gpr .rdx = s.gpr .rdx + s.gpr .r9 ∧ s'.gpr .rcx = s.gpr .rcx - s.gpr .r9 ∧ Keep [.rdx, .rcx] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [toPending, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      execAlu, Option.bind_some, gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags]
    rfl, ?_⟩
  refine ⟨?_, by rw [gpr_setReg_self], fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_arithFlags, gpr_setReg_self]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_setReg_of_ne _ _ hr.2, gpr_arithFlags, gpr_setReg_of_ne _ _ hr.1]

theorem cbcArgs_ok (s : State) (h : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa cbcArgs s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi ∧ s'.gpr .rsi = s.gpr .rdi + 128 ∧ s'.gpr .rdx = s.gpr .r8 - s.gpr .rsi ∧
      s'.gpr .rcx = (s.gpr .r9 + s.gpr .rsi) >>> 3 ∧
      s'.gpr .r8 = s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      Keep [.r8, .r9, .rdx, .rcx, .rsi] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [cbcArgs, rr, memOp, runBlock_cons, runStep_some, runBlock_nil,
      exec, readSrc, execAlu, execShift, State.load64, State.ea, offset_nat, Option.bind_some, Option.map_some,
      gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags, gpr_setFlags, rd_setReg, wr_setReg, rd_arithFlags,
      wr_arithFlags, rd_setFlags, wr_setFlags, mem_setReg, mem_arithFlags, mem_setFlags, h, ite_true]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals try simp (config := {decide := true}) only [gpr_setReg_self, gpr_setReg_of_ne, gpr_arithFlags,
    gpr_setFlags, ne_eq, reduceCtorEq, not_false_eq_true]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hr
    simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_setReg_of_ne _ _ h₃,
      gpr_setReg_of_ne _ _ h₄, gpr_setReg_of_ne _ _ h₅, gpr_arithFlags, gpr_setFlags]

end VG.Proof.Rc2.X86_64.Stream
