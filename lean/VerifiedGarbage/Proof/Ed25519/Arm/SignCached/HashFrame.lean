import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Calls
import VerifiedGarbage.Proof.Sha512.Stream

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay}

def slots (L : Lay) : Region := ⟨State.addr L.E, 24⟩
def hashWrites (L : Lay) : List Region := [L.SCR, slots L, digest L]

theorem setup_frame {m n : Mem} (hf : Frame [slots L] m n) : Frame (hashWrites L) m n :=
  hf.sub fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨slots L, by simp [hashWrites], fun _ h => h⟩

theorem hash_frame {m n : Mem} {rs : List Region} (hf : Frame rs m n)
    (hw : ∀ r ∈ rs, Whole.Within r L.SCR ∨ Whole.Within r (digest L)) : Frame (hashWrites L) m n := by
  refine hf.sub fun r hr => ?_
  rcases hw r hr with hc | hd
  · exact ⟨L.SCR, by simp [hashWrites], hc.sub⟩
  · exact ⟨digest L, by simp [hashWrites], hd.sub⟩

theorem frame_bytes {m n : Mem} {ws : List Region} (hf : Frame ws m n) (r : Region)
    (hd : ∀ w ∈ ws, r.Disjoint w) (hn : r.len ≤ 2 ^ 64) :
    Spec.Ed25519.bytesAt n r.base r.len = Spec.Ed25519.bytesAt m r.base r.len := by
  unfold Spec.Ed25519.bytesAt
  apply List.map_congr_left
  intro i hi
  exact Frame.bytes hf hd hn (List.mem_range.mp hi)

theorem setup_repr {m n : Mem} (hL : L.Ok) (hf : Frame [slots L] m n) {msg : List Byte}
    (hr : Spec.Sha512.Repr Spec.Sha512.H0_512 m (State.addr L.scr) msg) :
    Spec.Sha512.Repr Spec.Sha512.H0_512 n (State.addr L.scr) msg := by
  refine Proof.Sha512.Stream.repr_congr (mem := m) ?_ hr
  intro i hi
  exact hf.bytes (R := ⟨State.addr L.scr, 192⟩) (by
    rintro r hm; rw [List.mem_singleton.mp hm]
    exact (hL.kc.sub_left (Region.sub_prefix (by decide))).symm.sub_left (Region.sub_prefix (by decide)))
    (by change 192 ≤ 2 ^ 64; decide) hi

theorem hash_field_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n)
    {d : Nat} (hd : d + 32 ≤ 184) (hmin : 24 ≤ d) :
    Spec.Ed25519.bytesAt n (State.addr L.E + BitVec.ofNat 64 d) 32 =
      Spec.Ed25519.bytesAt m (State.addr L.E + BitVec.ofNat 64 d) 32 := by
  apply frame_bytes hf (field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact field_scr hL (by omega)
  · exact Offset.disjoint_base _ (by omega) (by omega)
  · exact Offset.disjoint _ (by omega) (by omega) (by decide)

theorem hash_out_bytes {m n : Mem} (hL : L.Ok) (hf : Frame (hashWrites L) m n) :
    Spec.Ed25519.bytesAt n (State.addr L.out) 32 = Spec.Ed25519.bytesAt m (State.addr L.out) 32 := by
  apply frame_bytes hf (baseOut L) _ (by change 32 ≤ 2 ^ 64; decide)
  simp only [hashWrites, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hL.oc.sub_left (baseWithin L).sub
  · exact (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (Region.sub_prefix (by decide))
  · exact (hL.ko.sub_right (baseWithin L).sub).symm.sub_right (digestWithin L).sub

theorem bytes_length (m : Mem) (p : Addr) (n : Nat) :
    (Spec.Ed25519.bytesAt m p n).length = n := by simp [Spec.Ed25519.bytesAt]

end VG.Proof.Ed25519.Arm.SignCached
