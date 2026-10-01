import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.HashFrame
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Reduce
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Base
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.MulAdd

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay} {m n : Mem}

theorem single_frame_bytes {d e k : Nat} (hf : Frame [⟨State.addr L.E + BitVec.ofNat 64 e, k⟩] m n)
    (hd : d + 32 ≤ 248) (he : e + k ≤ 248) (hs : d + 32 ≤ e ∨ e + k ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  rintro r hr; rw [List.mem_singleton.mp hr]
  exact Offset.disjoint _ hs (by omega) (by omega)

theorem reduce_field_bytes (hL : L.Ok) {d out : Nat} (hf : Frame (reduceWr L out) m n)
    (hd : d + 32 ≤ 248) (ho : out + 32 ≤ 248) (hs : d + 32 ≤ out ∨ out + 32 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.disjoint _ hs (by omega) (by omega)
  · exact field_scr hL hd

theorem base_field_bytes (hL : L.Ok) (hf : Frame (baseWr L) m n) {d : Nat} (hd : d + 32 ≤ 248) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact (hL.ko.sub_left (fieldWithin L hd).sub).sub_right (baseWithin L).sub
  · exact field_scr hL hd

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (reduceWr L d) m n) (hd : d + 32 ≤ 248) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact ((hL.ko.sub_left (fieldWithin L hd).sub).sub_right (baseWithin L).sub).symm
  · exact hL.oc.sub_left (baseWithin L).sub

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (mulWr L) m n) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact Offset.base_disjoint _ (by decide) (by decide)
  · exact hL.oc.sub_left (baseWithin L).sub

end VG.Proof.Ed25519.Arm.SignCached
