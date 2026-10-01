import VerifiedGarbage.Proof.TripleDes.X86_64.BlockIO
import VerifiedGarbage.Proof.TripleDes.Word

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

theorem packHalves_ok (s : State) :
    ∃ s', runBlock isa [rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] s = some s' ∧
      s'.gpr .rax = (s.gpr .r12).rotateRight 32 ^^^ s.gpr .r13 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, exec, execShift,
      readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact gpr_setReg_self _ _ _
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_false]

theorem storeTail_ok (s : State) :
    ∃ s', runBlock isa [.bswap .rbx, rr .rax .rbx] s = some s' ∧
      s'.gpr .rax = bswap64 (s.gpr .rbx) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
      Option.map_some, gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact gpr_setReg_self _ _ _
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hrax hrbx
    simp only [gpr_setReg, hrax, hrbx, ite_false]


theorem blockStore_run (s s₁ s₂ s₃ : State)
    (h₁ : runBlock isa [rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] s = some s₁)
    (h₂ : runBlock isa (permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) s₁ = some s₂)
    (h₃ : runBlock isa [.bswap .rbx, rr .rax .rbx] s₂ = some s₃) :
    runBlock isa blockStore s = some s₃ := by
  have hhead := runAppend_some _ _ _ _ _ h₁ h₂
  have htail := runAppend_some _ _ _ _ _ hhead h₃
  have hcode : blockStore =
      (([rr .rax .r12, .shift .ror .rax 32, .alu .xor .rax (.reg .r13)] : List Instr) ++
        permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp) ++ [.bswap .rbx, rr .rax .rbx] := rfl
  exact (congrArg (fun is => runBlock isa is s) hcode).trans htail

theorem blockStore_ok (s : State) (l r : BitVec 32)
    (hl : s.gpr .r12 = l.setWidth 64) (hr : s.gpr .r13 = r.setWidth 64) :
    ∃ s', runBlock isa blockStore s = some s' ∧
      s'.gpr .rax = bswap64 (Spec.TripleDes.permute Spec.TripleDes.fp (l ++ r)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], s'.gpr q = s.gpr q) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := packHalves_ok s
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, regs₂⟩ := final_raw_ok s₁
  obtain ⟨s₃, run₃, word₃, mem₃, rd₃, wr₃, regs₃⟩ := storeTail_ok s₂
  have hword : s₁.gpr .rax = l ++ r := by
    rw [hl, hr] at word₁
    exact word₁.trans (VG.Proof.TripleDes.packHalves_word l r)
  refine ⟨s₃, blockStore_run s s₁ s₂ s₃ run₁ run₂ run₃, ?_,
    mem₃.trans (mem₂.trans mem₁), rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact word₃.trans (congrArg bswap64 (word₂.trans
      (congrArg (Spec.TripleDes.permute Spec.TripleDes.fp) hword)))
  · intro q hq
    have hneq : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], q ≠ .rax ∧ q ≠ .rbx ∧ q ≠ .rbp := by decide
    have hdst : (instrs finalPermutation.lit).all
        (fun op => op.dst == some Reg.rbx || op.dst == some Reg.rbp) = true := by decide +kernel
    have hno : (instrs finalPermutation.lit).all (fun op => op.dst != some q) = true := by
      apply List.all_eq_true.mpr
      intro op hop
      have h := List.all_eq_true.mp hdst op hop
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · rw [h, bne_iff_ne]
        intro he
        exact (hneq q hq).2.1 (Option.some.inj he).symm
      · rw [h, bne_iff_ne]
        intro he
        exact (hneq q hq).2.2 (Option.some.inj he).symm
    exact (regs₃ q (hneq q hq).1 (hneq q hq).2.1).trans
      ((regs₂ q hno).trans (regs₁ q (hneq q hq).1))


theorem writeData_ok (s : State) (hwrite : InRegions s.wr (s.gpr .rsi) 8) :
    ∃ s', runBlock isa [.store (memOp .rsi 0) .rax] s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .rsi) (s.gpr .rax) ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have haddr : s.gpr .rsi + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .rsi := BitVec.add_zero _
  refine ⟨{ s with mem := s.mem.writeW (s.gpr .rsi) (s.gpr .rax) }, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
      State.ea, memOp, haddr, hwrite, ite_true], rfl, rfl, rfl, rfl⟩

end VG.Proof.TripleDes.X86_64
