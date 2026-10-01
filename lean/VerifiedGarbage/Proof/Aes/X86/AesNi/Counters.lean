import VerifiedGarbage.Proof.Aes.X86.AesNi.Arith
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (ctrs)

/-- The byte-order numeric counter word occupies the last memory dword;
the cached prefix has that dword zero. -/
def counterLane (c : BitVec 32) (pfx : BitVec 128) : BitVec 128 :=
  XBinOp.eval .por (XShiftOp.eval .pslldq ((0 : BitVec 96) ++ bswap c) 12) pfx

theorem counter_one (b : XReg) (s : State) (hb : b ≠ .xmm7) :
    WP isa (.block (ctrs [b])) s fun s' =>
      s'.xmm b = counterLane (s.gpr .ebx) (s.xmm .xmm7) ∧
      s'.gpr .ebx = s.gpr .ebx + 1 ∧
      (∀ r, r ≠ .eax → r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      (∀ r, r ≠ b → s'.xmm r = s.xmm r) := by
  apply WP.of_runBlock
  simp only [ctrs, List.append_nil]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, readSrc, XOp.exec, execAlu, counterLane, gpr_setReg,
    gpr_setXmm, xmm_setReg, xmm_setXmm, xmm_arithFlags, mem_setReg, rd_setReg,
    wr_setReg, ite_true, ite_false, Ne.symm hb, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · trivial
  · trivial
  · intro r heax hebx
    simp only [hebx, ite_false, gpr_arithFlags, gpr_setXmm, gpr_setReg, heax]
  · simp only [mem_arithFlags, mem_setXmm, mem_setReg]
  · simp only [rd_arithFlags, rd_setXmm, rd_setReg]
  · simp only [wr_arithFlags, wr_setXmm, wr_setReg]
  · intro r hr
    simp only [hr, ite_false]

end VG.Proof.Aes.X86.AesNi
