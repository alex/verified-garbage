import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashFinalize
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.HashInputs

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) : (Spec.Ed25519.bytesAt m p n).length = n := by
  simp only [Spec.Ed25519.bytesAt, List.length_map, List.length_range]

theorem hash_frame_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m')
    {d n : Nat} (hd : 24 ≤ d) (hn : d + n ≤ 192) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩) ?_ (by change n ≤ 2 ^ 64; omega) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.kc.sub_left (fun p hp => Whole.frame_sub L.E p (Offset.sub_base _ (by omega : d + n ≤ 256) p hp))
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · change Region.Disjoint _ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := n) (by omega)
  · exact Offset.disjoint _ (e := 192) (k := 64) (by omega) (by omega) (by decide)

theorem hash_out_bytes {L : Lay} (hL : L.Ok) {m m' : Mem} (hf : Frame (hashWrites L) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := ⟨L.out.setWidth 64, 32⟩) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  have ho : Region.Sub ⟨L.out.setWidth 64, 32⟩ L.OUT := Region.sub_prefix (by decide)
  rintro r (rfl | rfl | rfl | rfl)
  · exact hL.oc.sub_left ho
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right ho).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right ho).symm
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Offset.sub_base _ (by decide : 192 + 64 ≤ 256) p hp))).sub_right ho).symm

end VG.Proof.Ed25519.X86.SignCached
