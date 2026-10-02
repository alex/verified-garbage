import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Const
import VerifiedGarbage.Proof.Gcm.X86.GhashCT

namespace VG.Proof.Gcm.X86.Pclmul
open VG.X86 VG.X86.RegUpd
open VG.Impl.Gcm.X86.Pclmul (at_ argOp)
open VG.Proof.Gcm.X86 (GPre aR)

theorem args_in {s : State} (hp : GPre s) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s i) 4 := by
  refine ⟨aR s, by simp only [hp.rd, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_true, true_or], ?_⟩
  exact Proof.Aes.X86.part_contains (N := 24) (a := 4) (k := 20)
    hp.fSp (by decide) (by omega) (by omega) (by decide)

theorem ea_arg (s : State) (i : Nat) : s.ea (argOp i) = argAddr s i := rfl

theorem movArg_exec {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : i < 5)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hm : s.mem = s₀.mem)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (d : Reg) :
    exec (.mov d (.mem (argOp i))) s = some (s.setReg d (arg s₀ i)) := by
  have he : s.ea (argOp i) = argAddr s₀ i := by
    simp only [State.ea, argOp, at_, argAddr, hsp]
  simp only [exec, readSrc, State.load32, he, hrd, hwr, args_in hp hi,
    ite_true, hm, Option.map_some, arg]

/-- Load a big-endian GHASH block, retaining every general-purpose register. -/
theorem ldrev_ok (r : XReg) (b : Reg) (d : Nat) (s : State) (hr : r ≠ .xmm0)
    (h0 : s.xmm .xmm0 = VG.Proof.Gcm.X86.revMask)
    (hin : InRegions (s.rd ++ s.wr) (s.ea (at_ b d)) 16) :
    WP isa (.block [.movdquLoad r (at_ b d), .xop (.bin .pshufb r .xmm0)]) s fun s' =>
      s'.xmm r = Spec.Gcm.blockAt s.mem (s.ea (at_ b d)) ∧ Only [r] s s' := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec, isa, XOp.exec, State.load128, hin, ite_true, ite_false, xmm_setXmm, Ne.symm hr,
    h0, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp only [gpr_setXmm], by simp only [mem_setXmm],
    by simp only [rd_setXmm], by simp only [wr_setXmm], fun a ha => ?_⟩
  · rw [VG.Proof.Gcm.X86.blockAt_eq]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    simp only [xmm_setXmm, ha, ite_false]

end VG.Proof.Gcm.X86.Pclmul
