import VerifiedGarbage.Proof.Ed25519.Arm.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.Arm.DecodedThen

/-! Untrusted: the success branch follows the public decoder flag. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem decodedThen_ct {P : State → Prop} {next : Prog isa} (flag : Bool)
    (hp : ∀ s, P s → s.gpr .r9 = BitVec.ofNat 32 flag.toNat)
    (keep : ∀ s t, P s → Rest [] s t → t.mem = s.mem → P t)
    (yes : flag = true → CT (fun s t => P s ∧ P t) next (fun _ _ => True)) :
    CT (fun s t => P s ∧ P t) (decodedThen next) (fun _ _ => True) := by
  have hc : CT (fun s t => P s ∧ P t) (.block [.cmp .r9 (.imm 0)])
      (fun s t => (P s ∧ VG.Arm.eval .ne s = some flag) ∧ (P t ∧ VG.Arm.eval .ne t = some flag)) := by
    apply ctBoth
    · exact ctRegs [] (fun _ _ _ _ hr => (List.not_mem_nil hr).elim) (by taint_decide)
    · intro s hs
      refine wp_cmp (op2_imm (by decide)) fun t ht hz => WP.block_nil ⟨keep s t hs (ht.rest []) ht.mem, ?_⟩
      rw [VG.Arm.eval, hz, hp s hs]
      cases flag <;> rfl
  refine RelCT.seq hc (RelCT.ite (fun _ _ h => h.1.2.trans h.2.2.symm) ?_ ?_)
  · intro s t ts tt u v h ex ey
    have hy : flag = true := Option.some.inj (h.1.1.2.symm.trans h.2)
    exact yes hy _ _ _ _ _ _ ⟨h.1.1.1, h.1.2.1⟩ ex ey
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.Arm
