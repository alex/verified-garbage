import VerifiedGarbage.Proof.Ed25519.Arm.VerifyContract

/-! Untrusted: return the result and restore every callee-saved register. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem verifyFinish_ok {s : State} {b : BitVec 32} {g : Reg → BitVec 32}
    (hc : Ctx b s) (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block verifyFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧
      Rest [.r0, .r1, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11] s t ∧
      t.mem = s.mem ∧ t.gpr .r0 = s.gpr .r9 := by
  unfold verifyFinish
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_mov (op2_reg _ _) fun u hu => WP.block_nil ?_
  refine WP.mono (scalarRestore_ok (hc.of_rest (hu.rest (ws := [Reg.r1]) (by decide)) (by decide)) (hu.mem ▸ hs))
    fun v ⟨vg, vr, vm⟩ => ?_
  refine wp_mov (op2_reg _ _) fun t ht => WP.block_nil ?_
  refine ⟨fun i hi => ?_, (hu.rest (by decide)).trans ((vr.mono (by decide)).trans (ht.rest (by decide))),
    ht.mem.trans (vm.trans hu.mem), ?_⟩
  · rw [ht.other _ (by
      have h : ∀ i < 8, scalarSavedReg i ≠ Reg.r0 := by decide
      exact h i hi)]
    exact vg i hi
  · rw [ht.gpr, vr.gpr _ (by decide), hu.gpr]

end VG.Proof.Ed25519.Arm
