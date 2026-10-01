import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Hash

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86

def fp (L : Lay) (d : Nat) : BitVec 32 := L.E + BitVec.ofNat 32 d
def field (L : Lay) (d : Nat) : Region := ⟨(fp L d).setWidth 64, 32⟩

variable {L : Lay}

theorem fp_addr (hL : L.Ok) {d : Nat} (hd : d ≤ 256) :
    (fp L d).setWidth 64 = L.E.setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hL.top; omega)

theorem fieldWithin (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) : Whole.Within (field L d) L.FR :=
  ⟨d, fp_addr hL (by omega), by exact hd⟩

theorem field_sub (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) : Region.Sub (field L d) L.STK :=
  fun p hp => Whole.frame_sub L.E p ((fieldWithin hL hd).sub p hp)

theorem field_fit (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) : (fp L d).toNat + 32 ≤ 2 ^ 32 := by
  have he := hL.top
  simp only [fp, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := d) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem field_ce {g : Reg → BitVec 32} {m₀ : Mem} {s : State} (hc : Ctx L g m₀ s)
    (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt s.callEntry.mem ((fp L d).setWidth 64) 32 =
      Spec.Ed25519.bytesAt s.mem ((fp L d).setWidth 64) 32 := by
  apply Whole.callEntry_bytes (r := field L d) _ (by change 32 ≤ 2 ^ 64; decide)
  change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ ⟨(s.gpr .esp - BitVec.ofNat 32 4).setWidth 64, 4⟩
  rw [hc.esp, fp_addr hL (by omega), Taint.sub_setWidth (m := 4) (by have := hL.below; omega)]
  exact Offset.disjoint_below _ (n := 4) (d := d) (k := 32) (by omega)

theorem field_setup {m m' : Mem} (hL : L.Ok) (hf : Frame [⟨L.E.setWidth 64, 24⟩] m m')
    {d : Nat} (hd : 24 ≤ d) (hb : d + 32 ≤ 256) :
    Spec.Ed25519.bytesAt m' ((fp L d).setWidth 64) 32 = Spec.Ed25519.bytesAt m ((fp L d).setWidth 64) 32 := by
  unfold Spec.Ed25519.bytesAt
  refine List.map_congr_left fun i hi => ?_
  refine hf.bytes (R := field L d) ?_ (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rintro r hr; rw [List.mem_singleton.mp hr]
  change Region.Disjoint ⟨(fp L d).setWidth 64, 32⟩ _
  rw [fp_addr hL (by omega)]
  exact Offset.disjoint_base _ (d := d) (n := 32) (k := 24) hd (by omega)

def primitiveWrites (L : Lay) (out : Region) : List Region :=
  [out, L.SCR, ⟨L.E.setWidth 64, 24⟩, below L.E 24]

theorem primitive_frame {m m' m'' : Mem} {out : Region}
    (hf : Frame [⟨L.E.setWidth 64, 24⟩] m m')
    (hc : Frame ([out, L.SCR] ++ [below L.E 24]) m' m'') : Frame (primitiveWrites L out) m m'' := by
  refine (hf.sub ?_).trans (hc.sub ?_)
  · rintro r hr; rw [List.mem_singleton.mp hr]
    exact ⟨_, by simp [primitiveWrites], fun _ h => h⟩
  · intro r hr
    refine ⟨r, ?_, fun _ h => h⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [primitiveWrites]

end VG.Proof.Ed25519.X86.SignCached
