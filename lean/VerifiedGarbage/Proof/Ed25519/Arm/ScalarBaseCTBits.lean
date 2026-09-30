import VerifiedGarbage.Proof.Ed25519.Arm.BatchBits
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarBaseCTSupport

/-! Reloading the scalar pointer and batch index restores their public values. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def BitsCTPre (b p : BitVec 32) (j : Nat) (s : State) : Prop :=
  Ctx b s ∧ s.mem.readW (State.addr b + BitVec.ofNat 64 52) 32 = p ∧
    s.mem.readW (State.addr b + BitVec.ofNat 64 56) 32 = BitVec.ofNat 32 j

theorem batchBits_ct (b p : BitVec 32) (j : Nat) :
    CT (fun x y => BitsCTPre b p j x ∧ BitsCTPre b p j y)
      (.block batchBits) (fun x y => ∀ r ∈ ([.r0] : List Reg), x.gpr r = y.gpr r) := by
  let head : List Instr := [.ldr .r12 .r0 52, .ldr .r2 .r0 56]
  have hh : CT (fun x y => BitsCTPre b p j x ∧ BitsCTPre b p j y)
      (.block head) (fun x y => (x.gpr .r0 = b ∧ x.gpr .r12 = p ∧ x.gpr .r2 = BitVec.ofNat 32 j) ∧
        (y.gpr .r0 = b ∧ y.gpr .r12 = p ∧ y.gpr .r2 = BitVec.ofNat 32 j)) := by
    apply ctBoth
    · dsimp only [head]
      apply ctRegs [.r0] _ (by taint_decide)
      intro x y h r hr
      rw [List.mem_singleton] at hr
      subst r
      exact h.1.1.r0.trans h.2.1.r0.symm
    · intro s ⟨hc, hp, hj⟩
      refine ldr0_ok hc (by decide) fun u hu =>
        ldr0_ok (hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)) (by decide)
          fun t ht => WP.block_nil ?_
      refine ⟨(ht.other _ (by decide)).trans ((hu.other _ (by decide)).trans hc.r0),
        (ht.other _ (by decide)).trans (hu.gpr.trans hp), ?_⟩
      rw [ht.gpr, hu.mem]
      exact hj
  change CT _ (.block (head ++
    (([.dp .add .r12 .r12 (.shifted .r2 .lsl 1)] : List Instr) ++ unpackSrc 0 0 ++ expandBits))) _
  refine ctBlockAppend hh ?_
  dsimp only [head]
  apply ctRegsKeeping [.r0, .r12, .r2] [.r0] _ (by taint_decide)
  intro x y h r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact h.1.1.trans h.2.1.symm
  · exact h.1.2.1.trans h.2.2.1.symm
  · exact h.1.2.2.trans h.2.2.2.symm

end VG.Proof.Ed25519.Arm
