import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Prologue
import VerifiedGarbage.Proof.Framework.Offset

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd VG.Proof.Gcm.Poly
open VG.Proof.Gcm.X86 (GPre dP nBlk dR)
open VG.Impl.Gcm.X86.Pclmul (at_)

theorem data_read {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    InRegions (s.rd ++ s.wr) (s.ea (at_ .edx 0)) 16 := by
  have hf := hp.fD
  have he : s.ea (at_ .edx 0) = (dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i) := by
    simp only [State.ea, at_, hi.data, BitVec.add_zero]
    exact addr_eq (by omega)
  rw [he, hi.env.rd, hi.env.wr, hp.rd]
  refine ⟨dR s₀, ?_, Offset.contains_base _ (by omega) (by omega)⟩
  simp only [List.mem_append, List.mem_cons, or_true, true_or]

theorem xor_ok (s : State) :
    WP isa (.block [.xop (.bin .pxor .xmm2 .xmm7)]) s fun s' =>
      s'.xmm .xmm2 = s.xmm .xmm2 ^^^ s.xmm .xmm7 ∧ Only [.xmm2] s s' := by
  refine WP.of_runBlock ⟨s.setXmm .xmm2 (s.xmm .xmm2 ^^^ s.xmm .xmm7), ?_, ?_⟩
  · simp only [runBlock_cons, exec, XOp.exec, XBinOp.eval, runStep_some, runBlock_nil]
  · refine ⟨xmm_setXmm_self _ _ _, gpr_setXmm _ _ _, mem_setXmm _ _ _,
      rd_setXmm _ _ _, wr_setXmm _ _ _, ?_⟩
    intro r hr
    exact xmm_setXmm_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem advance_ok (s : State) :
    WP isa (.block [.alu .add .edx (.imm 16), .alu .sub .eax (.imm 1)]) s fun s' =>
      s'.gpr .eax = s.gpr .eax - 1 ∧ s'.gpr .edx = s.gpr .edx + 16 ∧
      s'.zf = some (s.gpr .eax - 1 == 0) ∧ Env s s' ∧
      s'.gpr .ecx = s.gpr .ecx ∧ s'.xmm = s.xmm := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, Option.bind_some, gpr_setReg, gpr_arithFlags,
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, rfl, ?_, True.intro, rfl⟩
  exact (((Env.refl s).arithFlags _ _ _).setReg .edx _ (by decide)).arithFlags _ _ _ |>.setReg .eax _ (by decide)

theorem body_ok {s₀ s : State} (hp : GPre s₀) {i : Nat} (hi : Inv s₀ i s)
    (hb : i < nBlk s₀) :
    WP isa (.block Impl.Gcm.X86.Pclmul.body) s fun s' =>
      Inv s₀ (i + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (i + 1) = 0)) := by
  simp only [Impl.Gcm.X86.Pclmul.body, List.append_assoc]
  rw [show ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0),
    .xop (.bin .pxor .xmm2 .xmm7)] : List Instr) =
    ([.movdquLoad .xmm7 (at_ .edx 0), .xop (.bin .pshufb .xmm7 .xmm0)] : List Instr) ++
    [.xop (.bin .pxor .xmm2 .xmm7)] from rfl,
    List.append_assoc, WP.block_append_iff]
  refine WP.mono (ldrev_ok .xmm7 .edx 0 s (by decide) hi.rev (data_read hp hi hb))
    fun s₁ ⟨input₁, f₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (xor_ok s₁) fun s₂ ⟨acc₂, f₂⟩ => ?_
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff]
  have poly₂ : s₂.xmm .xmm1 = Impl.Gcm.X86.Pclmul.poly := by
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.poly
  refine WP.mono (mul_ok s₂ poly₂) fun s₃ ⟨mul₃, f₃⟩ => ?_
  have env₃ := ((hi.env.of_only f₁).of_only f₂).of_only f₃
  have acc₃ : s₃.xmm .xmm2 = Y s₀ (i + 1) := by
    apply φ_inj
    have hin : s₁.xmm .xmm7 = Spec.Gcm.blockAt s₀.mem
        ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i)) := by
      rw [input₁, hi.env.mem]
      refine congrArg (Spec.Gcm.blockAt _) ?_
      simp only [State.ea, at_, hi.data, BitVec.add_zero]
      exact addr_eq (by have hf := hp.fD; omega)
    rw [mul₃, acc₂, hin, f₁.xmm _ (by decide), hi.acc]
    rw [f₂.xmm _ (by decide), f₁.xmm _ (by decide)]
    rw [mul_assoc, mul_left_comm x, hi.hash]
    rw [show Y s₀ (i + 1) = Spec.Gcm.mul (Y s₀ i ^^^ Spec.Gcm.blockAt s₀.mem
      ((dP s₀).setWidth 64 + BitVec.ofNat 64 (16 * i))) (H s₀) from
      Proof.Gcm.ghashFrom_blocksAt_succ _ _ _ _ _, φ_mul]
  refine WP.mono (advance_ok s₃) fun s₄ ⟨count₄, data₄, zf₄, ef₄, out₄, xmm₄⟩ => ?_
  have regs₃ : s₃.gpr = s.gpr := f₃.gpr.trans (f₂.gpr.trans f₁.gpr)
  have bound : nBlk s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have count : s₃.gpr .eax - 1 = BitVec.ofNat 32 (nBlk s₀ - (i + 1)) := by
    rw [regs₃, hi.count, Wp.ofNat_pred (by omega), Nat.sub_sub]
  constructor
  · refine ⟨env₃.trans ef₄, by omega, count₄.trans count, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [data₄, regs₃, hi.data, BitVec.add_assoc]
      change dP s₀ + (BitVec.ofNat 32 (16 * i) + BitVec.ofNat 32 16) = _
      rw [← BitVec.ofNat_add, show 16 * i + 16 = 16 * (i + 1) by omega]
    · rw [out₄, regs₃]; exact hi.out
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.rev
    · rw [xmm₄, f₃.xmm _ (by decide)]; exact poly₂
    · rw [xmm₄, f₃.xmm _ (by decide), f₂.xmm _ (by decide), f₁.xmm _ (by decide)]; exact hi.hash
    · rw [xmm₄]; exact acc₃
  · rw [zf₄, count, Wp.ofNat_beq_zero (by omega)]

end VG.Proof.Gcm.X86.Pclmul
