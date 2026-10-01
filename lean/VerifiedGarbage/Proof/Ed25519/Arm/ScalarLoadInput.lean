import VerifiedGarbage.Proof.Ed25519.Arm.ScalarMulAddArgs
import VerifiedGarbage.Proof.Ed25519.Arm.UnpackField
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec

/-! Load a scalar using a saved public input pointer. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

theorem scalarLoadInput_ok {b p : BitVec 32} {o ptrOff : Nat} {s : State} (hc : Ctx b s)
    (ho : o + 64 ≤ 4096) (hm : ptrOff + 4 ≤ 4096)
    (hp : s.mem.readW (State.addr b + BitVec.ofNat 64 ptrOff) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32)
    (hr : (⟨State.addr p, 32⟩ : Region) ∈ s.rd ++ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩) :
    WP isa (.block (scalarLoadInput o ptrOff)) s fun t =>
      Rest [.r2, .r3, .r12] s t ∧ Frame [⟨State.addr b + BitVec.ofNat 64 o, 64⟩] s.mem t.mem ∧
      Lim t.mem (State.addr b) o ∧ V t.mem (State.addr b) o =
        Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr p) 32) := by
  unfold scalarLoadInput
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc hm fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.mono (unpackField_ok (p := p) (src := 0) hcu ho (by decide) (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.rd, hu.wr]; simpa only [Nat.zero_add] using in_base hr (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using hsep.sub_right (Offset.sub_base _ (by omega))))
    fun t ⟨kt, ft, lt, vt⟩ => ?_
  refine ⟨(hu.rest (by decide)).trans (kt.mono (by decide)), ?_, lt, ?_⟩
  · rw [← hu.mem]; exact ft
  · rw [vt, hu.mem, BitVec.add_zero, scalar_packed_decode]

end VG.Proof.Ed25519.Arm
