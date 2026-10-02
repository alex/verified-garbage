import VerifiedGarbage.Proof.Aes.X86.AesNi.KeyArith
import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd

namespace VG.Proof.Aes.X86.AesNi
open VG.X86 VG.X86.RegUpd
open VG.Impl.Aes.X86.AesNi (at_ kstep kstepB6)

theorem ea_setXmm (st : State) (d : XReg) (v : BitVec 128) (a : MemOp) :
    (st.setXmm d v).ea a = st.ea a := rfl

theorem kstep_exec (d s : XReg) (sel r : BitVec 8) (off : Nat) (st : State) (hd3 : d ≠ .xmm3)
    (hd4 : d ≠ .xmm4) (hw : InRegions st.wr (st.ea (at_ .edx off)) 16) :
    WP isa (.block (kstep d s sel r off)) st fun st' =>
      st'.xmm d = kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel) ∧
      st'.mem = st.mem.writeW (st.ea (at_ .edx off))
        (kv (st.xmm d) (shufDwords (aesKeygenAssist (st.xmm s) r) sel)) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ d → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [kstep, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, State.store128, ea_setXmm, hw, ite_true, ite_false, hd3, hd4, Ne.symm hd3, Ne.symm hd4,
    Option.some.injEq, exists_eq_left', eval_movdqa, pslldq4, eval_pxor']
  exact ⟨rfl, rfl, trivial, trivial, trivial, fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩

theorem kstepB6_exec (off : Nat) (st : State)
    (hw : InRegions st.wr (st.ea (at_ .edx off)) 16) :
    WP isa (.block (kstepB6 off)) st fun st' =>
      st'.xmm .xmm2 = kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff) ∧
      st'.mem = st.mem.writeW (st.ea (at_ .edx off))
        (kb (st.xmm .xmm2) (shufDwords (st.xmm .xmm1) 0xff)) ∧
      st'.gpr = st.gpr ∧ st'.rd = st.rd ∧ st'.wr = st.wr ∧
      ∀ x, x ≠ .xmm2 → x ≠ .xmm3 → x ≠ .xmm4 → st'.xmm x = st.xmm x := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [kstepB6, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, xmm_setXmm, gpr_setXmm, mem_setXmm, rd_setXmm, wr_setXmm, State.store128, ea_setXmm, hw, ite_true, ite_false,
    Option.some.injEq, exists_eq_left', eval_movdqa, pslldq4, eval_pxor']
  exact ⟨rfl, rfl, trivial, trivial, trivial, fun x h1 h2 h3 => by simp only [h1, h2, h3, ite_false]⟩


end VG.Proof.Aes.X86.AesNi
