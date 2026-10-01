import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Calls

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def mulRd (L : Lay) : List Region := [field L 88, field L 120, field L 24, ⟨State.addr L.E, 4⟩]
def mulWr (L : Lay) : List Region := [half L, L.SCR]
def MulArgs (L : Lay) (s : State) : Prop :=
  s.gpr .r0 = L.out + 32 ∧ s.gpr .r1 = L.E + 88 ∧ s.gpr .r2 = L.E + 120 ∧
    s.gpr .r3 = L.E + 24 ∧ stackArg s 0 = L.scr

theorem mul_noFrames : scalarMulAdd.noFrames = true := by lit_decide

theorem mul_pre (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (mulRd L) (mulWr L)) := by
  have ao : State.addr (L.out + 32) = State.addr L.out + 32 := addr_add (k := 32) (by have := hL.no; omega)
  have fo : (L.out + 32).toNat + 32 ≤ 2 ^ 32 := by
    have hn := hL.no
    change (L.out.toNat + 32) % 2 ^ 32 + 32 ≤ 2 ^ 32
    rw [Nat.mod_eq_of_lt (by omega : L.out.toNat + 32 < 2 ^ 32)]
    omega
  have st : stackArg (s.callEntry.withRegions (mulRd L) (mulWr L)) 0 = stackArg s 0 := rfl
  have a88 : State.addr (L.E + 88) = State.addr L.E + 88 := frame_addr hL (d := 88) (by decide)
  have a120 : State.addr (L.E + 120) = State.addr L.E + 120 := frame_addr hL (d := 120) (by decide)
  have a24 : State.addr (L.E + 24) = State.addr L.E + 24 := frame_addr hL (d := 24) (by decide)
  have he := hc.sp
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp,
    State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), st,
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2, ao, he,
    a88, a120, a24]
  exact ⟨rfl, rfl, hL.oc.sub_left (halfWithin L).sub,
    field_scr hL (by decide), field_scr hL (by decide), field_scr hL (by decide),
    (hL.ko.sub_right (halfWithin L).sub).symm.sub_right (Region.sub_prefix (by decide)),
    hL.kc.symm.sub_right (Region.sub_prefix (by decide)), fo,
    frame_fit hL (by decide), frame_fit hL (by decide), frame_fit hL (by decide),
    hL.nc, by have := hL.top; omega⟩

theorem mul_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g m₀ t ∧
      Frame (mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.out + 32) 32 =
        Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 88) 32)
          (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 120) 32)
          (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 24) 32) := by
  have cov : Covers (mulRd L ++ mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl ⟨0, by simp, by change 0 + 4 ≤ 248; decide⟩
    · exact .inr (output_covered (halfWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (halfWithin L))
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarMulAdd_ok mul_noFrames (mul_pre hc hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  have ao : State.addr (L.out + 32) = State.addr L.out + 32 := addr_add (k := 32) (by have := hL.no; omega)
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarMulAdd (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r2)) 32)
      (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r3)) 32) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1] at hp
  have a88 : State.addr (L.E + 88) = State.addr L.E + 88 := frame_addr hL (d := 88) (by decide)
  have a120 : State.addr (L.E + 120) = State.addr L.E + 120 := frame_addr hL (d := 120) (by decide)
  have a24 : State.addr (L.E + 24) = State.addr L.E + 24 := frame_addr hL (d := 24) (by decide)
  rw [ao, a88, a120, a24] at hp
  exact hp

end VG.Proof.Ed25519.Arm.SignCached
