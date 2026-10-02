import VerifiedGarbage.Proof.TripleDes.Arm.Loop
namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.TripleDes.Arm

def startPointer (ptr : BitVec 32) (offset : Int) : BitVec 32 :=
  if offset < 0 then ptr - BitVec.ofNat 32 offset.natAbs else ptr + BitVec.ofNat 32 offset.natAbs

theorem passOffset_encodable : ∀ offset ∈ ([0, 120, 136, 376, -120, -136] : List Int),
    encodable (BitVec.ofNat 32 offset.natAbs) = true := by decide +kernel

theorem passStart_ok (offset : Int) (s : State)
    (ho : encodable (BitVec.ofNat 32 offset.natAbs) = true) :
    ∃ s', runBlock isa (passStart offset) s = some s' ∧
      s'.gpr .r0 = startPointer (s.gpr .r0) offset ∧ s'.gpr .r9 = 16 ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧
      (∀ r, r ≠ .r0 → r ≠ .r9 → s'.gpr r = s.gpr r) := by
  by_cases h : offset < 0
  all_goals refine ⟨(s.setReg .r0 (startPointer (s.gpr .r0) offset)).setReg .r9 16, by
    simp only [passStart, h, ite_true, ite_false, runBlock_cons, exec, Op2.eval, ho, ite_true,
      Option.map_some, imm, runStep_some, startPointer]
    rfl, ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  all_goals try simp only [gpr_setReg, startPointer, h, ite_true, ite_false, reduceCtorEq]
  all_goals try rfl
  all_goals
    intro r hr₀ hr₉
    simp only [hr₀, hr₉, ite_false]
end VG.Proof.TripleDes.Arm
