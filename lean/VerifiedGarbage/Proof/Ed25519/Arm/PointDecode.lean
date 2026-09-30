import VerifiedGarbage.Proof.Ed25519.Arm.DecodeLoad
import VerifiedGarbage.Proof.Ed25519.Decode

/-! Untrusted: the public byte decoder matches the reviewed strict specification. -/
namespace VG.Proof.Ed25519.Arm
open VG VG.Arm VG.Impl.Ed25519.Arm

theorem pointDecode_ok {s : State} {base ptr : BitVec 32} (hc : Ctx base s) (hl : AllLim s.mem base)
    (hp : s.gpr .r12 = ptr) (hfit : ptr.toNat + 32 ≤ 2 ^ 32)
    (hr : ∀ i < 32, InRegions (s.rd ++ s.wr) (State.addr ptr + BitVec.ofNat 64 i) 1)
    (hsep : (⟨State.addr ptr, 32⟩ : Region).Disjoint ⟨State.addr base, 8192⟩) :
    WP isa pointDecode s fun t => DecodeKeep base s t ∧ AllLim t.mem base ∧
      DecodeResult base (Spec.Ed25519.decodePoint (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32)) t := by
  have hlen : (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32).length = 32 := by
    simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]
  refine WP.seq (WP.mono (pointDecodeLoad_ok hc hl hp hfit hr hsep) fun a ⟨ak, al, asign, ay, az⟩ => ?_)
  apply WP.ite (decide (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (State.addr ptr) 32) % 2 ^ 255 < Spec.X25519.P))
    (by simp only [VG.Arm.eval, az])
  · intro ht
    have hy := of_decide_eq_true ht
    refine WP.mono (recoverPoint_ok (ak.ctx hc) al _ asign) fun t ⟨tk, tl, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_ikeep tk), tl, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_left hy]
    rw [ay] at tr
    exact tr
  · intro hf
    have hy := of_decide_eq_false hf
    refine WP.mono (recoverInvalid_ok a base) fun t ⟨tk, tm, tr⟩ => ?_
    refine ⟨ak.trans (DecodeKeep.of_keep tk), tm ▸ al, ?_⟩
    rw [decodePoint32 _ hlen, ite_eq_right hy]
    exact tr

end VG.Proof.Ed25519.Arm
