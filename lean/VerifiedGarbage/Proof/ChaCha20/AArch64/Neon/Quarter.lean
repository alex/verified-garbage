import VerifiedGarbage.Proof.ChaCha20.AArch64.Neon.Lanes

namespace VG.Proof.ChaCha20.AArch64.Neon

open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Neon
open VG.Spec.ChaCha20 (quarterRound)

/-- The four vector lanes execute four independent RFC 8439 quarter rounds. -/
theorem qr_ok (s : State) :
    WP isa (.block qr) s fun s' =>
      (∀ e, e < 4 →
        let q := quarterRound (vword (s.v .v0) e) (vword (s.v .v1) e)
          (vword (s.v .v2) e) (vword (s.v .v3) e)
        vword (s'.v .v0) e = q.1 ∧ vword (s'.v .v1) e = q.2.1 ∧
        vword (s'.v .v2) e = q.2.2.1 ∧ vword (s'.v .v3) e = q.2.2.2) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [qr, xorRot, List.cons_append, List.nil_append,
    runBlock_cons, runBlock_nil, exec, VOp.eval,
    ite_true, ite_false, Option.map_some, isa, runStep_some, Option.some.injEq, exists_eq_left',
    RegUpd.v_setV, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, RegUpd.sp_setV]
  refine ⟨fun e he => ?_, by trivial⟩
  simp only [vword_map2 _ _ _ he, vword_xor, VShiftOp.eval, shr_mask _ 16 (by decide),
    shr_mask _ 12 (by decide), shr_mask _ 8 (by decide), shr_mask _ 7 (by decide),
    quarterRound, BitVec.rotateLeft_def]
  simp only [Nat.reduceMod, Nat.reduceSub, BitVec.or_comm, and_self]

end VG.Proof.ChaCha20.AArch64.Neon
