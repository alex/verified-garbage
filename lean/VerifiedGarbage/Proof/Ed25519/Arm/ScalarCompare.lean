import VerifiedGarbage.Proof.Ed25519.Arm.ScalarPass

/-! A canonical-scalar check for the public verification inputs. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarCompare_ok {b : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) :
    WP isa (.block scalarCompare) s fun t =>
      Rest [.r2, .r3, .r4, .r5, .r6] s t ∧
      Frame [⟨State.addr b + BitVec.ofNat 64 SD, 64⟩] s.mem t.mem ∧
      (t.gpr .r5).toNat = if V s.mem (State.addr b) SR < Spec.Ed25519.L then 0 else 1 := by
  unfold scalarCompare
  simp only [List.cons_append, List.nil_append]
  refine wp_movw fun u hu => wp_mov (op2_imm (by decide)) fun v hv => ?_
  have kv : Rest [.r5, .r6] s v := (hu.rest (by decide)).trans (hv.rest (by decide))
  have mv : v.mem = s.mem := by rw [hv.mem, hu.mem]
  have hcv := hc.of_rest kv (by decide)
  refine WP.mono (scalarSubtractPass_ok hcv (mv ▸ hl) (by rw [hv.gpr]; rfl)
    (by rw [hv.other _ (by decide), hu.gpr])) fun t ht => ?_
  refine ⟨(kv.mono (by decide)).trans (ht.rest.mono (by decide)), ?_, ?_⟩
  · have hf := ht.frame; rwa [hcv.r0, mv] at hf
  · rw [ht.r5, mv, scalarCompare_carry (V_lt hl)]
    rfl

end VG.Proof.Ed25519.Arm
