import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Calls
import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Args
import VerifiedGarbage.Impl.Ed25519.Arm.VerifyMessage

namespace VG.Proof.Ed25519.Arm.VerifyMessage
open VG VG.Arm
open VG.Impl.Ed25519.Arm (scalarReduce)

def reduceRd (L : Lay) : List Region := [digest L]
def reduceWr (L : Lay) (d : Nat) : List Region := [field L d, L.SCR]
def ReduceArgs (L : Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .r0 = L.E + BitVec.ofNat 32 d ∧ s.gpr .r1 = L.E + 184 ∧ s.gpr .r2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd L) (reduceWr L d)) := by
  have ad := frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := frame_addr hL (d := 184) (by decide)
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2, ad, a184]
  have sep : (field L d).Disjoint (digest L) := Offset.disjoint _ (by omega) (by omega) (by decide)
  exact ⟨rfl, rfl, sep,
    field_scr hL (by omega), hL.kc.sub_left (digestWithin L).sub,
    frame_fit hL (by omega), frame_fit hL (by decide), hL.nc⟩

theorem reduce_call (hc : Ctx L g m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184)
    (ha : ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx L g m₀ t ∧
      Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E + 184) 64) := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by omega))
    · exact .inr (scratchWithin L)
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL hd ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  change Spec.Ed25519.bytesAt t.mem (State.addr (s.callEntry.gpr .r0)) 32 =
    Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr (s.callEntry.gpr .r1)) 64) at hp
  rw [State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.r1 ∉ linkRegs), ha.1, ha.2.1] at hp
  have ad := frame_addr hL (d := d) (by omega)
  have a184 : State.addr (L.E + 184) = State.addr L.E + 184 := frame_addr hL (d := 184) (by decide)
  rw [ad, a184] at hp
  exact hp

theorem reduce_step (hc : Ctx L g m₀ s) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (VG.Impl.Ed25519.Arm.Whole.callWith VG.Impl.Ed25519.Arm.VerifyMessage.reduceArgs "vg_ed25519_scalar_reduce" scalarReduce) s
      fun t => Ctx L g m₀ t ∧ Frame (reduceWr L 120) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (State.addr L.E+120) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (State.addr L.E+184) 64) := by
  refine WP.seq (WP.mono (args_regs_ok hc hL ha
    (args := [(.r0,.frame 120),(.r1,.frame 184),(.r2,.caller 4 0)])
    (by simp) (by simp [valid]) (by simp [preserved])) fun u ⟨hu,hm,hs⟩ => ?_)
  have a0 := hs (.r0,.frame 120) (by simp)
  have a1 := hs (.r1,.frame 184) (by simp)
  have a2 := hs (.r2,.caller 4 0) (by simp)
  change u.gpr .r2 = L.scr+0#32 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (reduce_call hu hL (d := 120) (by decide) ⟨a0,a1,a2⟩) fun t ⟨ht,hf,hp⟩ => ⟨ht,?_,?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.Arm.VerifyMessage
