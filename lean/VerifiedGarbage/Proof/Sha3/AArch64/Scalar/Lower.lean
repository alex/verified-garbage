import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

private theorem read_x (s : VG.AArch64.State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, Size.bits, BitVec.setWidth_eq]
private theorem write_gpr (s : VG.AArch64.State) (d r : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr r = if r = d then v else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

private theorem rotate_zero (x : BitVec 64) : x.rotateRight 0 = x := by
  simp only [BitVec.rotateRight, Nat.zero_mod, BitVec.rotateRightAux,
    BitVec.ushiftRight_zero, Nat.sub_zero, BitVec.shiftLeft_eq_zero (by decide : 64 ≤ 64), BitVec.or_zero]

/-- Every scalar register value agrees with the abstract file. -/
def RegRel (f : File) (s : VG.AArch64.State) : Prop := ∀ r, s.gpr r = f.regs r

/-- Register-only abstract operations run through the existing ISA. -/
theorem reg_lower_ok (op : ScalarOp) (hgood : Good op)
    (hmem : ∀ k r, op ≠ .spill k r) (hload : ∀ r k, op ≠ .reload r k)
    (f : File) (s : VG.AArch64.State) (hr : RegRel f s) :
    ∃ s', runBlock isa (lower op) s = some s' ∧ RegRel (step f op) s' ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ v, v ≠ .v29 → s'.v v = s.v v) := by
  change ∀ r, s.gpr r = f.regs r at hr
  cases op with
  | spill k r => exact False.elim (hmem k r rfl)
  | reload r k => exact False.elim (hload r k rfl)
  | xor d a b =>
    refine ⟨s.write .x d (s.gpr a ^^^ s.gpr b), ?_, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_logic, read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | move d a =>
    refine ⟨s.write .x d (s.gpr a), ?_, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_addImm_x (by decide : 0 < 4096),
        read_x, show (BitVec.ofNat 64 0) = 0 from rfl, Size.bits, runStep_some, runBlock_nil]
      exact congrArg (fun v => some (s.write .x d v)) (BitVec.add_zero (s.gpr a))
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | ror d a n =>
    refine ⟨s.write .x d ((s.gpr a).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_ror_x hgood, read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | bic d a b =>
    refine ⟨s.write .x d (s.gpr a &&& ~~~s.gpr b), ?_, ?_, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_bicRor (by decide : 0 < Size.x.bits),
        read_x, rotate_zero, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | bicRor d a b n =>
    refine ⟨s.write .x d (s.gpr a &&& ~~~(s.gpr b).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_bicRor (show n < Size.x.bits from hgood),
        read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]
  | xorRor d a b n =>
    refine ⟨s.write .x d (s.gpr a ^^^ (s.gpr b).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_logicRor (show n < Size.x.bits from hgood),
        read_x, runStep_some, runBlock_nil]
    · intro r
      simp only [step, File.write, write_gpr]
      split <;> simp only [hr]

end VG.Proof.Sha3.AArch64.Scalar
