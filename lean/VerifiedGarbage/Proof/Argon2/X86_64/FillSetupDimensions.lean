import VerifiedGarbage.Impl.Argon2.X86_64.FillSetup
import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
import VerifiedGarbage.Proof.Argon2.X86_64.Initialize
import VerifiedGarbage.Proof.Argon2.Dimensions

/-! Initialization's byte stride gives exact block and segment counts without division instructions. -/

namespace VG.Proof.Argon2.X86_64.FillSetup

open VG VG.X86_64 VG.Spec.Argon2

theorem dimensions_ok (s : State) : WP isa (.block Impl.Argon2.X86_64.FillSetup.dimensions) s fun t =>
    t.gpr .r12 = s.gpr .r13 >>> 10 ∧ t.gpr .r13 = s.gpr .r13 >>> 12 ∧ Divide.Keeps [.r12, .r13] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.X86_64.FillSetup.dimensions, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execShift, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    show 1 ≤ (10 : Nat) ∧ (10 : Nat) ≤ 63 from by decide,
    show 1 ≤ (12 : Nat) ∧ (12 : Nat) ≤ 63 from by decide,
    and_self, reduceCtorEq, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]
  all_goals rfl

theorem stride_shift (q shift : Nat) (bound : 1024 * q < 2 ^ 64) :
    BitVec.ofNat 64 (1024 * q) >>> shift = BitVec.ofNat 64 ((1024 * q) / 2 ^ shift) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) bound)]

theorem dimensions_nat_ok (s : State) (p : Params) (bound : 1024 * p.laneLen < 2 ^ 64)
    (stride : s.gpr .r13 = BitVec.ofNat 64 (1024 * p.laneLen)) :
    WP isa (.block Impl.Argon2.X86_64.FillSetup.dimensions) s fun t =>
      t.gpr .r12 = BitVec.ofNat 64 p.laneLen ∧ t.gpr .r13 = BitVec.ofNat 64 p.segmentLen ∧
      Divide.Keeps [.r12, .r13] s t := by
  refine (dimensions_ok s).mono ?_
  rintro t ⟨lane, segment, keeps⟩
  refine ⟨?_, ?_, keeps⟩
  · rw [lane, stride, stride_shift _ 10 bound]
    simp only [show 2 ^ 10 = 1024 from rfl, Nat.mul_div_cancel_left _ (by decide : 0 < 1024)]
  · rw [segment, stride, stride_shift _ 12 bound]
    have div : 1024 * p.laneLen / 4096 = p.laneLen / 4 := by
      rw [show (4096 : Nat) = 1024 * 4 from rfl, Nat.mul_div_mul_left _ _ (by decide : 0 < 1024)]
    rw [show 2 ^ 12 = 4096 from rfl, div]
    rfl

end VG.Proof.Argon2.X86_64.FillSetup
