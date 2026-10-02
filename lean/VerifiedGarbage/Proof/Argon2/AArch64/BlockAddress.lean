import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitScale
import VerifiedGarbage.Proof.Framework.AArch64.RelCT

/-! Fault-free matrix pointer calculation, with no memory accesses. -/

namespace VG.Proof.Argon2.AArch64.BlockAddress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.BlockAddress
open VG.Impl.Argon2.AArch64

theorem flatten_ok (s : State) : WP isa (.block flatten) s fun t =>
    t.gpr .x8 = s.gpr .x8 * s.gpr .x20 + s.gpr .x3 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  apply WP.of_runBlock
  simp only [flatten, Instructions.mul, Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem scale_ok (s : State) : WP isa (.block scale) s fun t =>
    t.gpr .x8 = s.gpr .x8 * 1024 ∧ Divide.Keeps [.x8, .x15] s t := by
  refine (MemoryInit.scale_ok s .x8 10).mono ?_
  intro t h
  refine ⟨h.value, ?_, h.mem, h.rd, h.wr, h.sp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact h.other r hr.1 hr.2

theorem base_ok (s : State) : WP isa (.block ([Instructions.add .x8 .x4].flatten)) s fun t =>
    t.gpr .x8 = s.gpr .x8 + s.gpr .x4 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x8 = (s.gpr .x8 * s.gpr .x20 + s.gpr .x3) * 1024 + s.gpr .x4 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold code
  refine WP.seq ((flatten_ok s).mono ?_)
  rintro a ⟨flat, ka⟩
  refine WP.seq ((scale_ok a).mono ?_)
  rintro b ⟨scaled, kb⟩
  refine (base_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ka.trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [result, scaled, flat, kb.regs .x4 (by decide), ka.regs .x4 (by decide)]

theorem code_nat_ok (s : State) (lane column q : Nat)
    (hl : s.gpr .x8 = BitVec.ofNat 64 lane)
    (hc : s.gpr .x3 = BitVec.ofNat 64 column)
    (hq : s.gpr .x20 = BitVec.ofNat 64 q) :
    WP isa code s fun t =>
      t.gpr .x8 = s.gpr .x4 + BitVec.ofNat 64 ((lane * q + column) * 1024) ∧
      Divide.Keeps [.x8, .x2, .x15] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨h, k⟩
  refine ⟨?_, k⟩
  rw [h, hl, hc, hq, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  change BitVec.ofNat 64 (lane * q + column) * BitVec.ofNat 64 1024 + s.gpr .x4 = _
  rw [← BitVec.ofNat_mul, BitVec.add_comm]

theorem code_secret_rel : RelCT isa (fun s t => s.sp = t.sp) code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [])
    (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) (by taint_decide)

end VG.Proof.Argon2.AArch64.BlockAddress
