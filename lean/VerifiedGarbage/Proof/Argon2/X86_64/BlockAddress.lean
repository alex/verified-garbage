import VerifiedGarbage.Impl.Argon2.X86_64.BlockAddress
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitScale
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-! Fault-free matrix pointer calculation, with no memory accesses. -/

namespace VG.Proof.Argon2.X86_64.BlockAddress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.BlockAddress

theorem flatten_ok (s : State) : WP isa (.block flatten) s fun t =>
    t.gpr .rax = s.gpr .rax * s.gpr .r12 + s.gpr .rcx ∧
    Divide.Keeps [.rax, .rdx] s t := by
  apply WP.of_runBlock
  simp only [flatten, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.some.injEq,
    exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2, ite_false]
  all_goals rfl

theorem scale_ok (s : State) : WP isa (.block scale) s fun t =>
    t.gpr .rax = s.gpr .rax * 1024 ∧ Divide.Keeps [.rax] s t := by
  refine WP.mono_mx (by decide +kernel) (MemoryInit.scale_ok s .rax 10) ?_
  intro t h mx
  refine ⟨h.value, ?_, h.mem, h.rd, h.wr, mx⟩
  intro r hr
  exact h.other r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)

theorem base_ok (s : State) : WP isa (.block [.alu .add .rax (.reg .r8)]) s fun t =>
    t.gpr .rax = s.gpr .rax + s.gpr .r8 ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [ite_true], ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .rax = (s.gpr .rax * s.gpr .r12 + s.gpr .rcx) * 1024 + s.gpr .r8 ∧
    Divide.Keeps [.rax, .rdx] s t := by
  unfold code
  refine WP.seq ((flatten_ok s).mono ?_)
  rintro a ⟨flat, ka⟩
  refine WP.seq ((scale_ok a).mono ?_)
  rintro b ⟨scaled, kb⟩
  refine (base_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ka.trans ((kb.mono (by simp)).trans (kt.mono (by simp)))⟩
  rw [result, scaled, flat, kb.regs .r8 (by decide), ka.regs .r8 (by decide)]

theorem code_nat_ok (s : State) (lane column q : Nat)
    (hl : s.gpr .rax = BitVec.ofNat 64 lane)
    (hc : s.gpr .rcx = BitVec.ofNat 64 column)
    (hq : s.gpr .r12 = BitVec.ofNat 64 q) :
    WP isa code s fun t =>
      t.gpr .rax = s.gpr .r8 + BitVec.ofNat 64 ((lane * q + column) * 1024) ∧
      Divide.Keeps [.rax, .rdx] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨h, k⟩
  refine ⟨?_, k⟩
  rw [h, hl, hc, hq, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  change BitVec.ofNat 64 (lane * q + column) * BitVec.ofNat 64 1024 + s.gpr .r8 = _
  rw [← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_secret_rel : RelCT isa (fun _ _ => True) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)

end VG.Proof.Argon2.X86_64.BlockAddress
