import VerifiedGarbage.Proof.TripleDes.X86_64.Bytes
import VerifiedGarbage.Proof.TripleDes.X86_64.Initial
import VerifiedGarbage.Proof.TripleDes.Core
import VerifiedGarbage.Impl.TripleDes.X86_64.Block
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.TripleDes.X86_64.Box

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64

theorem readData_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    ∃ s', runBlock isa
      [.mov .rax (.mem (memOp .rsi 0)), .bswap .rax] s = some s' ∧
      s'.gpr .rax = Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  have haddr : s.gpr .rsi + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .rsi :=
    BitVec.add_zero _
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
      State.ea, memOp, haddr, hread, ite_true, Option.map_some,
      gpr_setReg_self]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg_self]
    exact (decodeBlock_readW s.mem (s.gpr .rsi)).symm
  · simp only [mem_setReg]
  · simp only [rd_setReg]
  · simp only [wr_setReg]
  · intro r hr
    simp only [gpr_setReg, hr, ite_false]

theorem splitHalves_ok (s : State) :
    ∃ s', runBlock isa [rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] s = some s' ∧
      s'.gpr .r12 = s.gpr .rbx >>> 32 ∧
      s'.gpr .r13 = ((s.gpr .rbx).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r12 → r ≠ .r13 → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [rr, runBlock_cons, runStep_some, exec, readSrc, execShift,
      Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [State.setReg32, gpr_setReg, gpr_setFlags, reduceCtorEq, ite_true, ite_false]
  · exact gpr_setReg_self _ _ _
  · simp only [State.setReg32, mem_setReg, mem_setFlags]
  · simp only [State.setReg32, rd_setReg, rd_setFlags]
  · simp only [State.setReg32, wr_setReg, wr_setFlags]
  · intro r h12 h13
    simp only [State.setReg32, gpr_setReg, gpr_setFlags, h12, h13, ite_false]


theorem upperHalf_extend (x : BitVec 64) :
    x >>> 32 = ((x >>> 32).setWidth 32).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  by_cases h : j < 32
  · simp only [h, hj, decide_true, Bool.true_and]
  · have hz : x.getLsbD (32 + j) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    simp only [h, hj, decide_false, decide_true, Bool.false_and, Bool.true_and, hz]

theorem runAppend_some (xs ys : List Instr) (s t u : State)
    (hx : runBlock isa xs s = some t) (hy : runBlock isa ys t = some u) :
    runBlock isa (xs ++ ys) s = some u := by
  calc
    runBlock isa (xs ++ ys) s = (runBlock isa xs s).bind (runBlock isa ys) :=
      runBoxes_append xs ys s
    _ = (some t).bind (runBlock isa ys) := congrArg (fun v => v.bind (runBlock isa ys)) hx
    _ = runBlock isa ys t := Option.bind_some t (runBlock isa ys)
    _ = some u := hy

theorem blockLoad_run (s s₁ s₂ s₃ : State)
    (h₁ : runBlock isa [.mov .rax (.mem (memOp .rsi 0)), .bswap .rax] s = some s₁)
    (h₂ : runBlock isa (permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) s₁ = some s₂)
    (h₃ : runBlock isa [rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] s₂ = some s₃) :
    runBlock isa blockLoad s = some s₃ := by
  have hhead := runAppend_some _ _ _ _ _ h₁ h₂
  have htail := runAppend_some _ _ _ _ _ hhead h₃
  have hcode : blockLoad =
      (([.mov .rax (.mem (memOp .rsi 0)), .bswap .rax] : List Instr) ++
        permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp) ++
      [rr .r12 .rbx, .shift .shr .r12 32, .mov32 .r13 (.reg .rbx)] := rfl
  exact (congrArg (fun is => runBlock isa is s) hcode).trans htail

theorem blockLoad_ok (s : State)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8) :
    ∃ s', runBlock isa blockLoad s = some s' ∧
      s'.gpr .r12 =
        (((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)))) >>> 32).setWidth 32).setWidth 64 ∧
      s'.gpr .r13 =
        ((Spec.TripleDes.permute Spec.TripleDes.ip
          (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi)))).setWidth 32).setWidth 64 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rsp], s'.gpr r = s.gpr r) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, regs₁⟩ := readData_ok s hread
  obtain ⟨s₂, run₂raw, word₂, rd₂, wr₂, mem₂, regs₂⟩ := initial_raw_ok s₁
  obtain ⟨s₃, run₃, left₃, right₃, mem₃, rd₃, wr₃, regs₃⟩ := splitHalves_ok s₂
  have hword : s₂.gpr .rbx = Spec.TripleDes.permute Spec.TripleDes.ip
      (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt s.mem (s.gpr .rsi))) := by
    exact word₂.trans (congrArg (Spec.TripleDes.permute Spec.TripleDes.ip) word₁)
  refine ⟨s₃, ?_, ?_, ?_, mem₃.trans (mem₂.trans mem₁),
    rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁), ?_⟩
  · exact blockLoad_run s s₁ s₂ s₃ run₁ run₂raw run₃
  · exact left₃.trans ((congrArg (fun x : BitVec 64 => x >>> 32) hword).trans
      (upperHalf_extend _))
  · exact right₃.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hword)
  · intro r hr
    have hdst : (instrs initialPermutation.lit).all
        (fun op => op.dst == some Reg.rbx || op.dst == some Reg.rbp) = true := by
      decide +kernel
    have hneDst : r ≠ .rbx ∧ r ≠ .rbp := by
      have hfinite : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], q ≠ .rbx ∧ q ≠ .rbp := by decide
      exact hfinite r hr
    have hno : (instrs initialPermutation.lit).all
        (fun op => op.dst != some r) = true := by
      apply List.all_eq_true.mpr
      intro op hop
      have h := List.all_eq_true.mp hdst op hop
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      rcases h with h | h
      · rw [h, bne_iff_ne]
        intro he
        exact hneDst.1 (Option.some.inj he).symm
      · rw [h, bne_iff_ne]
        intro he
        exact hneDst.2 (Option.some.inj he).symm
    have hne : r ≠ .rax ∧ r ≠ .r12 ∧ r ≠ .r13 := by
      have hfinite : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp],
          q ≠ .rax ∧ q ≠ .r12 ∧ q ≠ .r13 := by decide
      exact hfinite r hr
    exact (regs₃ r hne.2.1 hne.2.2).trans ((regs₂ r hno).trans (regs₁ r hne.1))


end VG.Proof.TripleDes.X86_64
