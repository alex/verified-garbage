import VerifiedGarbage.Impl.Ed25519.AArch64.RecoverSign
import VerifiedGarbage.Proof.Ed25519.AArch64.FieldCheck

/-! The public sign bit is compared to the canonical x-coordinate. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

def signWord (b : Bool) : BitVec 64 := if b then 1 else 0

theorem parity_flag (w : BitVec 64) (b : Bool) :
    ((w &&& BitVec.ofNat 64 1) ^^^ signWord b == 0) = ((w.toNat % 2 == 1) == b) := by
  have hw : w &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (w.toNat % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, show (BitVec.ofNat 64 1).toNat = 1 from rfl,
      Nat.and_one_is_mod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show w.toNat % 2 < 2 ^ 64 by omega)]
  rw [hw]
  have h : w.toNat % 2 = 0 ∨ w.toNat % 2 = 1 := by omega
  rcases h with h | h <;> rw [h] <;> cases b <;> decide

theorem recoverParity_ok {s : State} (b : Bool) (hs : s.gpr .x1 = signWord b) :
    WP isa (.block recoverParity) s fun t =>
      (t.gpr .x8 == 0) = (((val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 == 1) == b)) ∧
      Keeps [.x9, .x8] s t := by
  have hv : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) % 2 = (s.gpr .x4).toNat % 2 := by
    simp only [val4]; omega
  apply WP.of_runBlock
  simp only [recoverParity, runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, ite_true, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', hs, hv]
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · exact parity_flag _ b
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem returnFlag_ok (s : State) (b : Bool) :
    WP isa (.block [.movz .w .x8 (if b then 1 else 0) 0]) s fun t =>
      t.gpr .x8 = signWord b ∧ Keeps [.x8] s t := by
  cases b <;> apply WP.of_runBlock <;>
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, show 16 * 0 < Size.w.bits from by decide, ite_true,
      Option.some.injEq, exists_eq_left']
  all_goals
    refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

end VG.Proof.Ed25519.AArch64
