import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.Calls
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyVerified

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

def challenge (L : Lay) : Region := ⟨L.E+128,64⟩
def equationRd (L : Lay) : List Region := [L.PK,L.SIG,challenge L]
def equationWr (L : Lay) : List Region := [L.SCR]
def EqArgs (L : Lay) (s : State) : Prop := s.gpr .x0 = L.pk ∧
  s.gpr .x1 = L.sig ∧ s.gpr .x2 = L.E+128 ∧ s.gpr .x3 = L.scr

theorem equation_noFrames : verifyEquation.noFrames = true := by lit_decide

theorem challengeWithin (L : Lay) : Whole.Within (challenge L) L.FR :=
  ⟨128,rfl,by change 128+64≤256; decide⟩

theorem equation_pre (hL : L.Ok) (ha : EqArgs L s) :
    verifyLocal.pre (s.callEntry.withRegions (equationRd L) (equationWr L)) := by
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), ha.1,ha.2.1,ha.2.2.1,ha.2.2.2]
  exact ⟨rfl,rfl,hL.sc _ (by simp [Lay.inputs]),hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (challengeWithin L).sub,hL.nc⟩

theorem equation_covers : Covers (equationRd L ++ equationWr L) (L.inputs ++ L.FR :: L.outputs) := by
  apply covers
  simp only [equationRd,equationWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro r (rfl | rfl | rfl | rfl)
  · exact .inr ⟨L.PK,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inr ⟨L.SIG,by simp [Lay.inputs],0,by simp,by simp⟩
  · exact .inl (challengeWithin L)
  · exact .inr (scratch_covered L)

theorem equation_writes : ∀ r ∈ equationWr L,
    Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨L.SCR,by simp [Lay.outputs],scratchWithin L⟩

theorem equation_call (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : EqArgs L s) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => Ctx L g v m₀ t ∧
      t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine Whole.call_ok hc verify_ok equation_noFrames (equation_pre hL ha)
    equation_covers equation_writes fun t ht _ hp => ⟨ht,?_⟩
  change t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x0) 32)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x1) 64)
    (Spec.Ed25519.bytesAt s.mem (s.callEntry.gpr .x2) 64)) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),ha.1,ha.2.1,ha.2.2.1] at hp
  exact hp

theorem equation_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.AArch64.Whole.callWith VG.Impl.Ed25519.AArch64.VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation) s
      fun t => Ctx L g v m₀ t ∧ t.gpr .x0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem L.pk 32) (Spec.Ed25519.bytesAt s.mem L.sig 64)
        (Spec.Ed25519.bytesAt s.mem (L.E+128) 64)) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0,.caller 0 0),(.x1,.caller 3 0),(.x2,.frame 128),(.x3,.caller 4 0)])
    (by simp) (by simp [Whole.valid]) (by simp [known]) (by simp [preserved]))
    fun u ⟨hu,hm,hav⟩ => ?_)
  have a0 := hav (.x0,.caller 0 0) (by simp)
  have a1 := hav (.x1,.caller 3 0) (by simp)
  have a2 := hav (.x2,.frame 128) (by simp)
  have a3 := hav (.x3,.caller 4 0) (by simp)
  change u.gpr .x0 = L.pk+0#64 at a0
  change u.gpr .x1 = L.sig+0#64 at a1
  change u.gpr .x3 = L.scr+0#64 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  refine WP.mono (equation_call hu hL ⟨a0,a1,a2,a3⟩) fun t ⟨ht,hp⟩ => ⟨ht,?_⟩
  rw [hm] at hp
  exact hp

end VG.Proof.Ed25519.AArch64.VerifyMessage
