import VerifiedGarbage.Impl.Ed25519.AArch64.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.AArch64.PointAccumulate

/-! Untrusted: the counter of the descending-bit loops. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem accumulateDec_ok (s : State) (n : Nat)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x19 .x19 1]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem CounterKeep.refl (base : Addr) (s : State) : CounterKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem accumulateInit_ok (s : State) :
    WP isa (.block [.movz .w .x19 16 0]) s fun t => t.gpr .x19 = 16 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self]; rfl
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)


end VG.Proof.Ed25519.AArch64
