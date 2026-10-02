import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Load

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64
open VG.Proof.Rc2.X86_64 (offset_nat)

def pack : List Instr := [rr .rax .r12, .shift .ror .rax 36, .alu .xor .rax (.reg .r13)]

def tail : List Instr := [.store (memOp .r15 0) .rbx, .alu .add .r15 (.imm 8),
  .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm 16)]

theorem pack_ok (s : State) (c d : BitVec 28)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64) :
    ∃ s', runBlock isa pack s = some s' ∧
      (s'.gpr .rax).setWidth 56 = c ++ d ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) := by
  refine ⟨_, by
    simp only [pack, rr, runBlock_cons, runStep_some, exec, execShift,
      readSrc, Option.map_some, gpr_setReg, ite_true]
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hc, hd]
    exact VG.Proof.TripleDes.pack28_word c d
  · simp only [mem_setReg, mem_setFlags, mem_arithFlags]
  · simp only [rd_setReg, rd_setFlags, rd_arithFlags]
  · simp only [wr_setReg, wr_setFlags, wr_arithFlags]
  · intro r hr
    simp only [gpr_setReg, gpr_setFlags, gpr_arithFlags, hr, ite_false]

theorem nextRound_values : ∀ j < 16,
    BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j + 1) ∧
    ((BitVec.ofNat 64 j + 1 - (16 : BitVec 64)) == 0) = decide (j = 15) := by decide

theorem tail_ok (s : State) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r14 = BitVec.ofNat 64 j)
    (hw : InRegions s.wr (s.gpr .r15) 8) :
    ∃ s', runBlock isa tail s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r15) (s.gpr .rbx) ∧
      s'.gpr .r15 = s.gpr .r15 + 8 ∧ s'.gpr .r14 = BitVec.ofNat 64 (j + 1) ∧
      s'.zf = some (decide (j = 15)) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ .r14 → r ≠ .r15 → s'.gpr r = s.gpr r) := by
  have hoff : s.gpr .r15 + BitVec.ofInt 64 (Int.ofNat 0) = s.gpr .r15 := BitVec.add_zero _
  refine ⟨_, by
    simp only [tail, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.store64, State.ea, memOp, hoff, hw, ite_true, Option.bind_some,
      gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false]
    rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rfl
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_true, ite_false]
    rw [hc]
    exact (nextRound_values j hj).1
  · rw [zf_arithFlags, hc]
    exact congrArg some (nextRound_values j hj).2
  · simp only [rd_setReg, rd_arithFlags]
  · simp only [wr_setReg, wr_arithFlags]
  · intro r h14 h15
    simp only [gpr_setReg, gpr_arithFlags, h14, h15, ite_false]

structure StorePost (c d : BitVec 28) (j : Nat) (s s' : State) : Prop where
  mem : s'.mem = s.mem.writeW (s.gpr .r15) ((Spec.TripleDes.permute Spec.TripleDes.pc2 (c ++ d)).setWidth 64)
  ptr : s'.gpr .r15 = s.gpr .r15 + 8
  counter : s'.gpr .r14 = BitVec.ofNat 64 (j + 1)
  flag : s'.zf = some (decide (j = 15))
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13], s'.gpr r = s.gpr r

theorem storeRound_ok (s : State) (c d : BitVec 28) (j : Nat) (hj : j < 16)
    (hc : s.gpr .r12 = c.setWidth 64) (hd : s.gpr .r13 = d.setWidth 64)
    (hjreg : s.gpr .r14 = BitVec.ofNat 64 j) (hw : InRegions s.wr (s.gpr .r15) 8) :
    WP isa (.block Impl.TripleDes.X86_64.Key.storeRound) s (StorePost c d j s) := by
  have code : Impl.TripleDes.X86_64.Key.storeRound =
      (pack ++ permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp) ++ tail := rfl
  rw [code, WP.block_append_iff, WP.block_append_iff]
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, reg₁⟩ := pack_ok s c d hc hd
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, word₂, rd₂, wr₂, mem₂, reg₂⟩ := pc2_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  rw [word₁] at word₂
  have checks : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15],
      ((instrs keyPermutation2.lit).all fun op => op.dst != some r) = true := by decide +kernel
  have keep₂ : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15], s₂.gpr r = s.gpr r := by
    intro r hr
    have unused : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15], r ≠ .rax := by decide
    exact (reg₂ r (checks r hr)).trans (reg₁ r (unused r hr))
  have counter₂ := (keep₂ .r14 (by decide)).trans hjreg
  have write₂ : InRegions s₂.wr (s₂.gpr .r15) 8 := by
    rw [wr₂, wr₁, keep₂ .r15 (by decide)]; exact hw
  obtain ⟨s₃, run₃, mem₃, ptr₃, counter₃, flag₃, rd₃, wr₃, reg₃⟩ := tail_ok s₂ j hj counter₂ write₂
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, counter₃, flag₃, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩⟩
  · rw [mem₃, mem₂, mem₁, keep₂ .r15 (by decide), word₂]
  · rw [ptr₃, keep₂ .r15 (by decide)]
  · intro r hr
    have incl : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13],
        r ≠ .r14 ∧ r ≠ .r15 ∧ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp, .r12, .r13, .r14, .r15] := by decide
    exact (reg₃ r (incl r hr).1 (incl r hr).2.1).trans (keep₂ r (incl r hr).2.2)

end VG.Proof.TripleDes.X86_64.Key
