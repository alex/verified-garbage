import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Calls
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Args
import VerifiedGarbage.Impl.Ed25519.Arm.VerifyMessage
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyVerified

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm VG.Impl.Ed25519.Arm

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

def signWord (b : Bool) : BitVec 32 := if b then 1 else 0

def challenge (L : Lay) : Region := ⟨State.addr L.E+120,64⟩
def equationRd (L : Lay) : List Region := [L.PK,L.SIG,challenge L]
def equationWr (L : Lay) : List Region := [L.SCR]
def EqArgs (L : Lay) (s : State) : Prop := s.gpr .r0 = L.pk ∧
  s.gpr .r1 = L.sig ∧ s.gpr .r2 = L.E+120 ∧ s.gpr .r3 = L.scr

theorem equation_noFrames : verifyEquation.noFrames = true := by lit_decide

theorem challengeWithin (L : Lay) : Whole.Within (challenge L) L.FR :=
  ⟨120,rfl,by change 120+64≤248; decide⟩

theorem equation_pre (hL : L.Ok) (ha : EqArgs L s) :
    verifyLocal.pre (s.callEntry.withRegions (equationRd L) (equationWr L)) := by
  have ac : State.addr (L.E+120) = State.addr L.E+120 := frame_addr hL (d := 120) (by decide)
  simp only [verifyLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r3 ∉ linkRegs), ha.1,ha.2.1,ha.2.2.1,ha.2.2.2,ac]
  exact ⟨rfl,rfl,hL.sc _ (by simp [Lay.inputs]),hL.sc _ (by simp [Lay.inputs]),
    hL.kc.sub_left (challengeWithin L).sub,hL.np,hL.ns,frame_fit hL (by decide),hL.nc⟩

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

theorem equation_call (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : EqArgs L s) :
    WP isa (.call "vg_ed25519_verify_equation" verifyEquation) s fun t => Ctx L g m₀ t ∧
      t.gpr .r0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem (State.addr L.pk) 32) (Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 64)
        (Spec.Ed25519.bytesAt s.mem (State.addr L.E+120) 64)) := by
  refine Whole.call_ok hc verify_ok equation_noFrames (equation_pre hL ha)
    equation_covers equation_writes fun t ht _ hp => ⟨ht,?_⟩
  change (t.gpr .r0).toNat = (if Spec.Ed25519.verifyEquation
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r0)) 32)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 64)
    (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r2)) 64) then 1 else 0) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs),ha.1,ha.2.1,ha.2.2.1] at hp
  have ac : State.addr (L.E+120) = State.addr L.E+120 := frame_addr hL (d := 120) (by decide)
  rw [ac] at hp
  apply BitVec.eq_of_toNat_eq
  rw [hp]
  cases Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (State.addr L.pk) 32) (Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 64) (Spec.Ed25519.bytesAt s.mem (State.addr L.E+120) 64) <;> rfl

theorem equation_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith VG.Impl.Ed25519.Arm.VerifyMessage.equationArgs "vg_ed25519_verify_equation" verifyEquation) s
      fun t => Ctx L g m₀ t ∧ t.gpr .r0 = signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt s.mem (State.addr L.pk) 32) (Spec.Ed25519.bytesAt s.mem (State.addr L.sig) 64)
        (Spec.Ed25519.bytesAt s.mem (State.addr L.E+120) 64)) := by
  refine WP.seq (WP.mono (args_regs_ok hc hL ha
    (args := [(.r0,.caller 0 0),(.r1,.caller 3 0),(.r2,.frame 120),(.r3,.caller 4 0)])
    (by simp) (by simp [valid]) (by simp [preserved]))
    fun u ⟨hu,hm,hav⟩ => ?_)
  have a0 := hav (.r0,.caller 0 0) (by simp)
  have a1 := hav (.r1,.caller 3 0) (by simp)
  have a2 := hav (.r2,.frame 120) (by simp)
  have a3 := hav (.r3,.caller 4 0) (by simp)
  change u.gpr .r0 = L.pk+0#32 at a0
  change u.gpr .r1 = L.sig+0#32 at a1
  change u.gpr .r3 = L.scr+0#32 at a3
  rw [BitVec.add_zero] at a0 a1 a3
  refine WP.mono (equation_call hu hL ⟨a0,a1,a2,a3⟩) fun t ⟨ht,hp⟩ => ⟨ht,?_⟩
  rw [hm] at hp
  exact hp

end VG.Proof.Ed25519.Arm.VerifyMessage
