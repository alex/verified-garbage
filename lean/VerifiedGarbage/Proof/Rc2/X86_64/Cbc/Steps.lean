import VerifiedGarbage.Proof.Rc2.X86_64.Cbc.Call
import VerifiedGarbage.Proof.Rc2.CbcMemory

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.X86_64.Cbc

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .rax)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (memOp src a)), .store (memOp dst b) .rax] s = some s' ∧
      Keep [.rax] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, memOp, exec, readSrc,
      State.load64, State.store64, State.ea, offset_nat, readable, ite_true,
      Option.map_some, gpr_setReg, hne, ite_false,
      wr_setReg, writable]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    exact gpr_setReg_of_ne _ _ hr
  · rfl
  · rfl
  · rfl

theorem xor64_ok (s : State) (dst iv : Reg) (hd : dst ≠ .rax) (hi : iv ≠ .rax)
    (readDst : InRegions (s.rd ++ s.wr) (s.gpr dst) 8)
    (readIv : InRegions (s.rd ++ s.wr) (s.gpr iv) 8)
    (writable : InRegions s.wr (s.gpr dst) 8) :
    ∃ s', runBlock isa [.mov .rax (.mem (memOp dst 0)), .alu .xor .rax (.mem (memOp iv 0)),
      .store (memOp dst 0) .rax] s = some s' ∧
      Keep [.rax] {s with mem := s.mem.writeW (s.gpr dst) (s.mem.readW (s.gpr dst) 64 ^^^ s.mem.readW (s.gpr iv) 64)} s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, memOp, exec, execAlu, readSrc,
      State.load64, State.store64, State.ea, offset_nat,
      BitVec.add_zero, readDst, readIv, ite_true, Option.map_some, Option.bind_some,
      gpr_setReg, gpr_arithFlags, mem_setReg, rd_setReg, wr_setReg, wr_arithFlags,
      hd, hi, ite_false, writable]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_singleton] at hr
    simp only [gpr_setReg, gpr_arithFlags, hr, ite_false]
  · rfl
  · rfl
  · rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.X86_64.Cbc.advance s = some s' ∧
      s'.gpr .rsi = s.gpr .rsi + 8 ∧ s'.gpr .rbp = s.gpr .rbp - 1 ∧
      s'.zf = some ((s.gpr .rbp - 1) == 0) ∧ Keep [.rsi, .rbp] s s' := by
  refine ⟨_, by
    simp (config := {decide := true}) only [Impl.Rc2.X86_64.Cbc.advance,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
      Option.bind_some, gpr_setReg, gpr_arithFlags, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_setReg, gpr_arithFlags, reduceCtorEq, ite_false, ite_true]
    rfl
  · exact gpr_setReg_self _ _ _
  · rw [zf_setReg, zf_arithFlags]
    rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_setReg, gpr_arithFlags, hr.1, hr.2, ite_false]
    · simp only [mem_setReg, mem_arithFlags]
    · simp only [rd_setReg, rd_arithFlags]
    · simp only [wr_setReg, wr_arithFlags]

end VG.Proof.Rc2.X86_64.Cbc
