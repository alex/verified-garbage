import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Calls

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarMulAdd)
open VG.Impl.Ed25519.AArch64.Whole (callWith)

def mulRd (L : Lay) : List Region := [field L 96, field L 128, field L 32]
def mulWr (L : Lay) : List Region := [half L, L.SCR]
def MulArgs (L : Lay) (s : State) : Prop :=
  s.gpr .x0 = L.out + 32 ∧ s.gpr .x1 = L.E + 96 ∧ s.gpr .x2 = L.E + 128 ∧
    s.gpr .x3 = L.E + 32 ∧ s.gpr .x4 = L.scr

theorem mul_noFrames : scalarMulAdd.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem mul_pre (hL : L.Ok) (ha : MulArgs L s) :
    scalarMulAddLocal.pre (s.callEntry.withRegions (mulRd L) (mulWr L)) := by
  simp only [scalarMulAddLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs),
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ha.2.2.2.2]
  exact ⟨rfl, rfl, field_scr hL (by decide), field_scr hL (by decide), field_scr hL (by decide), hL.nc⟩

theorem mul_call (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : MulArgs L s) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t => Ctx L g v m₀ t ∧
      Frame (mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) (Spec.Ed25519.bytesAt s.mem (L.E + 128) 32)
        (Spec.Ed25519.bytesAt s.mem (L.E + 32) 32) := by
  have cov : Covers (mulRd L ++ mulWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (output_covered (halfWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ mulWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (halfWithin L))
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarMulAdd_ok mul_noFrames (mul_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarMulAddLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1] using hp

theorem mul_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith mulAddArgs "vg_ed25519_scalar_mul_add" scalarMulAdd) s fun t =>
      Ctx L g v m₀ t ∧ Frame (mulWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.out + 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) (Spec.Ed25519.bytesAt s.mem (L.E + 128) 32)
        (Spec.Ed25519.bytesAt s.mem (L.E + 32) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 0 32) (by simp)
  have a1 := hs (.x1, .frame 96) (by simp)
  have a2 := hs (.x2, .frame 128) (by simp)
  have a3 := hs (.x3, .frame 32) (by simp)
  have a4 := hs (.x4, .caller 5 0) (by simp)
  change u.gpr .x4 = L.scr + 0#64 at a4
  rw [BitVec.add_zero] at a4
  refine WP.mono (mul_call hu hL ⟨a0, a1, a2, a3, a4⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
