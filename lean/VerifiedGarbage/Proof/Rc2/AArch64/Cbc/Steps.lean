import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Call
import VerifiedGarbage.Proof.Rc2.CbcMemory

/-! # CBC loads, XORs, stores, and public loop counters -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc2.AArch64

theorem copy64_ok (s : State) (src dst : Reg) (a b : Nat) (hne : dst ≠ .x8)
    (readable : InRegions (s.rd ++ s.wr) (s.gpr src + BitVec.ofNat 64 a) 8)
    (writable : InRegions s.wr (s.gpr dst + BitVec.ofNat 64 b) 8)
    (ha : a % 8 = 0 ∧ a < 32768 := by decide)
    (hb : b % 8 = 0 ∧ b < 32768 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x8 src a, .str .x .x8 dst b] s = some s' ∧
      Keep [.x8, .x9] {s with
        mem := s.mem.writeW (s.gpr dst + BitVec.ofNat 64 b) (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)} s' := by
  have hw : InRegions (s.write .x .x8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).wr
      ((s.write .x .x8 (s.mem.readW (s.gpr src + BitVec.ofNat 64 a) 64)).gpr dst + BitVec.ofNat 64 b) 8 := by
    simpa only [wr_write, gpr_write, hne, ite_false] using writable
  refine ⟨_, by
    rw [runBlock_cons, exec_ldr_x s _ _ a ha readable, runStep_some,
      runBlock_cons, exec_str_x _ _ _ b hb hw, runStep_some, runBlock_nil], ?_⟩
  constructor
  · intro r hr
    have hn : r ≠ .x8 := by intro h; subst r; exact hr (by simp)
    exact gpr_write_of_ne _ _ _ hn
  · simp only [gpr_write, hne, ite_false, ite_true, BitVec.setWidth_eq, mem_write]
  · rfl
  · rfl

theorem xor64_ok (s : State) (dst iv : Reg) (hd : dst ≠ .x8) (hi : iv ≠ .x8)
    (readDst : InRegions (s.rd ++ s.wr) (s.gpr dst) 8)
    (readIv : InRegions (s.rd ++ s.wr) (s.gpr iv) 8)
    (writable : InRegions s.wr (s.gpr dst) 8)
    (hd9 : dst ≠ .x9 := by decide) :
    ∃ s', runBlock isa [.ldr .x .x8 dst 0, .ldr .x .x9 iv 0,
      .logic .eor .x .x8 .x8 .x9, .str .x .x8 dst 0] s = some s' ∧
      Keep [.x8, .x9] {s with
        mem := s.mem.writeW (s.gpr dst) (s.mem.readW (s.gpr dst) 64 ^^^ s.mem.readW (s.gpr iv) 64)} s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      Nat.zero_mod, Nat.reduceMul, Nat.reduceLT, and_self, ite_true, Option.bind_some, State.load,
      State.store, State.read, BitVec.setWidth_eq, BitVec.add_zero,
      readDst, readIv, writable, Option.map_some, gpr_write, mem_write, rd_write, wr_write,
      hd, hi, hd9, reduceCtorEq, ite_false]
    rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_write, hr.1, hr.2, ite_false]
  · rfl
  · rfl
  · rfl

def zeroCount (s : State) : Option Bool := some (s.gpr .x24 == 0)

theorem eval_zeroCount (s : State) : eval (.zero .x .x24) s = zeroCount s := rfl

theorem eval_nonzeroCount (s : State) : eval (.nonzero .x .x24) s = (zeroCount s).map (! ·) := rfl

theorem advance_ok (s : State) :
    ∃ s', runBlock isa Impl.Rc2.AArch64.Cbc.advance s = some s' ∧
      s'.gpr .x1 = s.gpr .x1 + 8 ∧ s'.gpr .x24 = s.gpr .x24 - 1 ∧
      zeroCount s' = some ((s.gpr .x24 - 1) == 0) ∧ Keep [.x1, .x24] s s' := by
  refine ⟨_, by
    simp only [Impl.Rc2.AArch64.Cbc.advance, runBlock_cons, runStep_some, runBlock_nil,
      exec, State.read, BitVec.setWidth_eq, Nat.reduceLT, ite_true,
      gpr_write, reduceCtorEq, ite_false]
    rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · exact gpr_write_self _ _ _ _
  · rfl
  · constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [gpr_write, hr.1, hr.2, ite_false]
    · simp only [mem_write]
    · simp only [rd_write]
    · simp only [wr_write]

end VG.Proof.Rc2.AArch64.Cbc
