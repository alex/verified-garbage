import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lower
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64

namespace VG.Proof.Sha3.AArch64.Scalar
open VG VG.AArch64 VG.Impl.Sha3.AArch64.Scalar

private theorem exec_dup (s : VG.AArch64.State) (v : VReg) (r : Reg) :
    exec (.vop (.dup .d2 v r)) s =
      some (s.setV v (ofVDwords (s.gpr r) (s.gpr r))) := rfl
private theorem exec_umov (s : VG.AArch64.State) (r : Reg) (v : VReg) :
    exec (.umov .x r v 0) s = some (s.write .x r (vdword (s.v v) 0)) := rfl

private theorem read_x (s : VG.AArch64.State) (r : Reg) : s.read .x r = s.gpr r := by
  simp only [State.read, Size.bits, BitVec.setWidth_eq]
private theorem write_gpr (s : VG.AArch64.State) (d r : Reg) (v : BitVec 64) :
    (s.write .x d v).gpr r = if r = d then v else s.gpr r := by
  simp only [RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq]

/-- Every scalar register value agrees with the abstract file. -/
def RegRel (f : File) (s : VG.AArch64.State) : Prop := ∀ r, s.gpr r = f.regs r

private theorem bic_identity (a b : BitVec 64) : (a &&& b) ^^^ a = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

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
  | bicRor d a b n => exact False.elim hgood
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
    have hda : d ≠ a := hgood
    let t := s.write .x d (s.gpr a &&& s.gpr b)
    refine ⟨t.write .x d ((s.gpr a &&& s.gpr b) ^^^ s.gpr a), ?_, ?_, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩
    · simp only [lower, runBlock_cons, exec_logic, read_x, runStep_some, runBlock_nil,
        t, write_gpr, ite_true, ite_eq_right (Ne.symm hda)]
    · intro r
      simp only [step, File.write, t, write_gpr]
      split <;> simp only [hr, bic_identity]
  | xorRor d a b n =>
    obtain ⟨hn, halias⟩ := hgood
    by_cases hda : d = a
    · subst d
      have hab : a ≠ b := halias rfl
      let t := (s.setV .v29 (ofVDwords (s.gpr b) (s.gpr b))).write .x b ((s.gpr b).rotateRight n)
      let u := t.write .x a (s.gpr a ^^^ (s.gpr b).rotateRight n)
      refine ⟨u.write .x b (s.gpr b), ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
      · simp only [lower, eq_self, ite_true, t, u, runBlock_cons, exec_dup, runStep_some, exec_ror_x hn,
          exec_logic, exec_umov, runBlock_nil, read_x, write_gpr,
          RegUpd.gpr_setV, RegUpd.v_write, RegUpd.v_setV,
          ite_true, ite_eq_right hab, vdword_ofVDwords_0]
      · intro r
        simp only [step, File.write, u, t, write_gpr, RegUpd.gpr_setV]
        by_cases hra : r = a
        · subst r; simp only [ite_eq_right hab, ite_true, hr]
        · by_cases hrb : r = b
          · subst r; simp only [eq_self, ite_true, ite_eq_right (Ne.symm hab), hr]
          · simp only [ite_eq_right hra, ite_eq_right hrb, hr]
      · intro v hv
        simp only [u, t, RegUpd.v_write, RegUpd.v_setV, ite_eq_right hv]
    · let t := s.write .x d ((s.gpr b).rotateRight n)
      refine ⟨t.write .x d (s.gpr a ^^^ (s.gpr b).rotateRight n), ?_, ?_, rfl, rfl, rfl, rfl,
        fun _ _ => rfl⟩
      · simp only [lower, ite_eq_right hda, runBlock_cons, exec_ror_x hn, exec_logic, read_x,
          runStep_some, runBlock_nil, t, write_gpr, eq_self,
          ite_true, ite_eq_right (Ne.symm hda)]
      · intro r
        simp only [step, File.write, t, write_gpr]
        split <;> simp only [hr]

end VG.Proof.Sha3.AArch64.Scalar
