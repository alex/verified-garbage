import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.HashSteps

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64

variable {L : Lay}

theorem input_self {r : Region} (hr : r ∈ L.inputs) :
    ∃ R ∈ L.inputs ++ L.outputs, Whole.Within r R :=
  ⟨r, List.mem_append_left _ hr, 0, by simp, by simp⟩

theorem seed_input (hL : L.Ok) : Input L L.seed 32 :=
  ⟨.inr (input_self (r := L.SEED) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem key_input (hL : L.Ok) : Input L L.pk 32 :=
  ⟨.inr (input_self (r := L.PK) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem message_input (hL : L.Ok) : Input L L.msg L.len :=
  ⟨.inr (input_self (r := L.MSG) (by simp [Lay.inputs])), hL.sc _ (by simp [Lay.inputs])⟩
theorem point_input (hL : L.Ok) : Input L L.out 32 :=
  ⟨.inr (output_covered (baseWithin L)), hL.oc.sub_left (baseWithin L).sub⟩
theorem prefix_input (hL : L.Ok) : Input L (L.E + 64) 32 :=
  ⟨.inl (fieldWithin L (by decide)), field_scr hL (by decide)⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 192) :
    Spec.Ed25519.bytesAt n (L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact field_scr hL (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)
  · exact (Whole.ck_frame (by omega)).symm

theorem hash_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n) :
    Spec.Ed25519.bytesAt n L.out 32 = Spec.Ed25519.bytesAt m L.out 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oc.sub_left (baseWithin L).sub
  · exact (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (digestWithin L).sub
  · exact (hL.co.sub_right (baseWithin L).sub).symm

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.AArch64.SignCached
