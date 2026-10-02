import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Proof.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Proof.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Ed25519.Arm.InitFields

/-! All input scalar bits, exact point multiplication, and canonical encoding compose. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm VG.Proof.X25519.Arm

def encodedValue (p : Spec.Ed25519.Point) : Nat :=
  (p.Y * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val +
    ((p.X * Spec.X25519.pow p.Z (Spec.X25519.P - 2)).val % 2) * 2 ^ 255

theorem encodedValue_spec (p : Spec.Ed25519.Point) :
    Spec.Ed25519.encodePoint p = Spec.Ed25519.encodeLE 32 (encodedValue p) := rfl

theorem scalarBaseEngine_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa scalarBaseEngine s fun t => PointKeep base s t ∧ Lim t.mem (State.addr base) FR ∧
      V t.mem (State.addr base) FR = encodedValue
        (Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) Spec.Ed25519.basePoint) := by
  refine WP.seq (WP.mono (initFields_ok hc) fun a ⟨ak, al, _⟩ => ?_)
  refine WP.seq (WP.mono (fieldCode_ok (constPointOps Spec.Ed25519.basePoint) (ak.ctx hc) al)
    fun u ⟨uk, ul, ue⟩ => ?_)
  have ku := ak.trans uk
  have up : u.gpr .r12 = ptr := (ku.rest.gpr _ (by decide)).trans hp
  have ur : ∀ i < 32, InRegions (u.rd ++ u.wr) (State.addr ptr + BitVec.ofNat 64 i) 1 := by
    intro i hi
    rw [ku.rest.rd, ku.rest.wr]
    exact hr i hi
  have uv : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt u.mem (State.addr ptr) 32) =
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) := by
    rw [← packedDigits_decode _ _ 16, ← packedDigits_decode _ _ 16]
    exact packedDigits_frame ku.frame (by decide) fun r hm => by
      rw [List.mem_singleton.mp hm]
      exact hsep.sub_right (Offset.sub_base _ (by decide))
  have upp : point (env u.mem base) 0 1 2 3 = Spec.Ed25519.basePoint :=
    (congrArg (fun e => point e 0 1 2 3) ue).trans (constPoint_eval _ _)
  refine WP.seq (WP.mono (pointFromScalar_ok (ku.ctx hc) ul up 16 (by decide) (by decide) hfit ur hsep)
    fun v ⟨vk, vl, _, vp⟩ => ?_)
  have ksv := (PointKeep.of_keep ku).trans vk
  refine WP.mono (pointEncode_ok (ksv.ctx hc) vl) fun t ⟨tk, tl, tv⟩ => ?_
  refine ⟨ksv.trans (PointKeep.of_ikeep tk), tl, ?_⟩
  change V t.mem (State.addr base) FR = encodedValue (point (env v.mem base) 0 1 2 3) at tv
  exact tv.trans (congrArg encodedValue
    (vp.trans (congrArg₂ Spec.Ed25519.pointMul uv upp)))

end VG.Proof.Ed25519.Arm
