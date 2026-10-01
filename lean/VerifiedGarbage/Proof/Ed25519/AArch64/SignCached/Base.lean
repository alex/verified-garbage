import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Calls

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarBase)
open VG.Impl.Ed25519.AArch64.Whole (callWith)

def baseRd (L : Lay) : List Region := [field L 96]
def baseWr (L : Lay) : List Region := [baseOut L, L.SCR]
def BaseArgs (L : Lay) (s : State) : Prop :=
  s.gpr .x0 = L.out ∧ s.gpr .x1 = L.E + 96 ∧ s.gpr .x2 = L.scr

theorem base_noFrames : scalarBase.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem base_pre (hL : L.Ok) (ha : BaseArgs L s) :
    scalarBaseLocal.pre (s.callEntry.withRegions (baseRd L) (baseWr L)) := by
  simp only [scalarBaseLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, field_scr hL (by decide), hL.nc⟩

theorem base_call (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : BaseArgs L s) :
    WP isa (.call "vg_ed25519_scalar_base" scalarBase) s fun t => Ctx L g v m₀ t ∧
      Frame (baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) := by
  have cov : Covers (baseRd L ++ baseWr L) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [baseRd, baseWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (output_covered (baseWithin L))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ baseWr L, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [baseWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inr (.inl (baseWithin L))
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarBase_ok base_noFrames (base_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarBaseLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem base_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) s fun t =>
      Ctx L g v m₀ t ∧ Frame (baseWr L) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem L.out 32 =
        Spec.Ed25519.scalarBase (Spec.Ed25519.bytesAt s.mem (L.E + 96) 32) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)])
    (by decide) (by simp [Whole.valid]) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .caller 0 0) (by simp)
  have a1 := hs (.x1, .frame 96) (by simp)
  have a2 := hs (.x2, .caller 5 0) (by simp)
  change u.gpr .x0 = L.out + 0#64 at a0
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a0 a2
  refine WP.mono (base_call hu hL ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
