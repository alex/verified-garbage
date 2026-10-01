import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Base
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.MulAdd
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Reduce
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Hashes

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86
variable {L : Lay} {m m' : Mem}

theorem frame_bytes {rs : List Region} (hf : Frame rs m m') (r : Region)
    (hd : ∀ R ∈ rs, r.Disjoint R) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt m' r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  exact List.map_congr_left fun i hi => hf.bytes hd hn (List.mem_range.mp hi)

theorem single_frame_bytes {d n e k : Nat} (hf : Frame [⟨L.E.setWidth 64 + BitVec.ofNat 64 e, k⟩] m m')
    (hsep : d + n ≤ e ∨ e + k ≤ d) (hd : d + n ≤ 256) (he : e + k ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.E.setWidth 64 + BitVec.ofNat 64 d) n =
      Spec.Ed25519.bytesAt m (L.E.setWidth 64 + BitVec.ofNat 64 d) n :=
  frame_bytes hf ⟨L.E.setWidth 64 + BitVec.ofNat 64 d, n⟩
    (by rintro r hr; rw [List.mem_singleton.mp hr]; exact Offset.disjoint _ hsep (by omega) (by omega))
    (by change n ≤ 2 ^ 64; omega)

theorem primitive_field_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : (field L d).Disjoint out) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine frame_bytes hf (field L d) ?_ (by change 32 ≤ 2 ^ 64; decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.kc.sub_left (field_sub hL hb)
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ _
    rw [fp_addr hL (by omega)]
    exact Offset.disjoint_base _ hd (by omega)
  · change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(L.E - BitVec.ofNat 32 24).setWidth 64, 24⟩
    rw [fp_addr hL (by omega), Taint.sub_setWidth hL.below]
    exact Offset.disjoint_below _ (n := 24) (d := d) (k := 32) (by omega)

theorem reduce_field_bytes (hL : L.Ok) {o d : Nat}
    (hf : Frame (primitiveWrites L (field L o)) m m') (hd : 24 ≤ d) (hb : d + 32 ≤ 256)
    (ho : o + 32 ≤ 256) (hs : d + 32 ≤ o ∨ o + 32 ≤ d) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  refine primitive_field_bytes hL hf hd hb ?_
  change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(fp L o).setWidth 64, 32⟩
  rw [fp_addr hL (by omega), fp_addr hL (by omega)]
  exact Offset.disjoint _ hs (by omega) (by omega)

theorem base_field_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (baseOut L)) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 :=
  primitive_field_bytes hL hf hd hb ((hL.ko.sub_left (field_sub hL hb)).sub_right (Region.sub_prefix (by decide)))

theorem primitive_out_bytes (hL : L.Ok) {out : Region}
    (hf : Frame (primitiveWrites L out) m m') (ho : (baseOut L).Disjoint out) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine frame_bytes hf (baseOut L) ?_ (by change 32 ≤ 2 ^ 64; decide)
  have hs : Region.Sub (baseOut L) L.OUT := Region.sub_prefix (by decide)
  simp only [primitiveWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact ho
  · exact hL.oc.sub_left hs
  · exact ((hL.ko.sub_left (fun p hp => Whole.frame_sub L.E p
      (Region.sub_prefix (by decide : 24 ≤ 256) p hp))).sub_right hs).symm
  · exact ((hL.ko.sub_left (Whole.below_sub_stack hL.below (by decide))).sub_right hs).symm

theorem reduce_out_bytes (hL : L.Ok) {d : Nat} (hf : Frame (primitiveWrites L (field L d)) m m')
    (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 :=
  primitive_out_bytes hL hf (((hL.ko.sub_left (field_sub hL hd)).sub_right (Region.sub_prefix (by decide))).symm)

theorem mul_out_bytes (hL : L.Ok) (hf : Frame (primitiveWrites L (half L)) m m') :
    Spec.Ed25519.bytesAt m' (L.out.setWidth 64) 32 = Spec.Ed25519.bytesAt m (L.out.setWidth 64) 32 := by
  refine primitive_out_bytes hL hf ?_
  change Region.Disjoint ⟨L.out.setWidth 64, 32⟩ ⟨(L.out + 32).setWidth 64, 32⟩
  rw [half_addr hL]
  exact Offset.base_disjoint _ (e := 32) (n := 32) (k := 32) (by decide) (by decide)

theorem hash_field_bytes (hL : L.Ok) (hf : Frame (hashWrites L) m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 192) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  rw [fp_addr hL (by omega)]
  exact hash_frame_bytes hL hf hd hb

end VG.Proof.Ed25519.X86.SignCached
