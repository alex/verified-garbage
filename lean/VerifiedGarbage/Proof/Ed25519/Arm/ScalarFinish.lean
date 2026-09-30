import VerifiedGarbage.Proof.Ed25519.Arm.ScalarABI
import VerifiedGarbage.Proof.Ed25519.Arm.ScalarCodec

/-! Canonical scalar output and restoration of the saved registers. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

abbrev scalarFinishClob : List Reg := [.r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12]

theorem scalarFinish_ok {b p : BitVec 32} {s : State} (hc : Ctx b s)
    (hl : Lim s.mem (State.addr b) SR) (hp : s.mem.readW (State.addr b + 32) 32 = p)
    (hfit : p.toNat + 32 ≤ 2 ^ 32) (hw : (⟨State.addr p, 32⟩ : Region) ∈ s.wr)
    (hsep : (⟨State.addr p, 32⟩ : Region).Disjoint ⟨State.addr b, 8192⟩)
    {g : Reg → BitVec 32} (hs : ScalarSaved (State.addr b) g s.mem) :
    WP isa (.block scalarFinish) s fun t =>
      (∀ i < 8, t.gpr (scalarSavedReg i) = g (scalarSavedReg i)) ∧ Rest scalarFinishClob s t ∧
      Frame [⟨State.addr p, 32⟩] s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr p) 32 = Spec.Ed25519.encodeLE 32 (V s.mem (State.addr b) SR) := by
  rw [scalarFinish, List.append_assoc]
  simp only [List.cons_append, List.nil_append]
  refine ldr0_ok hc (by decide) fun u hu => ?_
  have hcu := hc.of_rest (hu.rest (ws := [.r12]) (by decide)) (by decide)
  refine WP.append (packField_ok (p := p) (a := SR) (dst := 0) hcu (by decide) (hu.mem ▸ hl) (by decide)
    (hu.gpr.trans hp) (by omega)
    (fun i hi => by rw [hu.wr]; simpa only [Nat.zero_add] using in_base hw (by omega) (by omega))
    (by simpa only [BitVec.add_zero] using
      hsep.symm.sub_left (Offset.sub_base _ (by decide : SR + 64 ≤ 8192))))
    fun v ⟨kv, fv, vv⟩ => ?_
  have hcv := hcu.of_rest kv (by decide)
  have hs' : ScalarSaved (State.addr b) g v.mem :=
    (hu.mem ▸ hs).frame fv fun r hr i hi => by
      rw [List.mem_singleton.mp hr, BitVec.add_zero]
      exact hsep.symm.sub_left (Offset.sub_base _ (by omega))
  refine WP.mono (scalarRestore_ok hcv hs') fun t ⟨saved, kt, mt⟩ => ?_
  refine ⟨saved, (hu.rest (by decide)).trans ((kv.mono (by decide)).trans (kt.mono (by decide))), ?_, ?_⟩
  · rw [mt, ← hu.mem]; simpa only [BitVec.add_zero] using fv
  · rw [mt, scalar_packed_encode, ← hu.mem]
    have e : packedV v.mem (State.addr p) = V u.mem (State.addr b) SR := by
      simpa only [BitVec.add_zero] using vv
    exact congrArg (Spec.Ed25519.encodeLE 32) e

end VG.Proof.Ed25519.Arm
