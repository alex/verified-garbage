import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Calls

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached
open VG.Impl.Ed25519.AArch64 (scalarReduce)

def reduceRd (L : Lay) : List Region := [digest L]
def reduceWr (L : Lay) (d : Nat) : List Region := [field L d, L.SCR]
def ReduceArgs (L : Lay) (d : Nat) (s : State) : Prop :=
  s.gpr .x0 = L.E + BitVec.ofNat 64 d ∧ s.gpr .x1 = L.E + 192 ∧ s.gpr .x2 = L.scr

theorem reduce_noFrames : scalarReduce.noFrames = true := by lit_decide

variable {L : Lay} {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {s : State}

theorem reduce_pre (hL : L.Ok) {d : Nat} (ha : ReduceArgs L d s) :
    scalarReduceLocal.pre (s.callEntry.withRegions (reduceRd L) (reduceWr L d)) := by
  simp only [scalarReduceLocal, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs), ha.1, ha.2.1, ha.2.2]
  exact ⟨rfl, rfl, hL.kc.sub_left (digestWithin L).sub⟩

theorem reduce_call (hc : Ctx L g v m₀ s) (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256)
    (ha : ReduceArgs L d s) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) s fun t => Ctx L g v m₀ t ∧
      Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  have cov : Covers (reduceRd L ++ reduceWr L d) (L.inputs ++ L.FR :: L.outputs) := by
    apply covers
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L hd)
    · exact .inr (scratch_covered L)
  have ws : ∀ r ∈ reduceWr L d, Whole.Within r L.FR ∨ ∃ R ∈ L.outputs, Whole.Within r R := by
    apply writes
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L hd)
    · exact .inr (.inr (scratchWithin L))
  refine Whole.call_ok hc scalarReduce_ok reduce_noFrames (reduce_pre hL ha) cov ws
    fun t ht hf hp => ⟨ht, hf, ?_⟩
  simpa only [scalarReduceLocal, State.withRegions_mem, State.withRegions_gpr,
    State.callEntry_mem, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs), ha.1, ha.2.1] using hp

theorem reduce_step (hc : Ctx L g v m₀ s) (hL : L.Ok) (ha : Arguments L m₀)
    (d : Nat) (hd : d + 32 ≤ 256) :
    WP isa (reduce d) s fun t => Ctx L g v m₀ t ∧ Frame (reduceWr L d) s.mem t.mem ∧
      Spec.Ed25519.bytesAt t.mem (L.E + BitVec.ofNat 64 d) 32 =
        Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt s.mem (L.E + 192) 64) := by
  refine WP.seq (WP.mono (args_ok hc hL ha
    (args := [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)])
    (by simp) (by simp [Whole.valid]; omega) (by simp [preserved])) fun u ⟨hu, hm, hs⟩ => ?_)
  have a0 := hs (.x0, .frame d) (by simp)
  have a1 := hs (.x1, .frame 192) (by simp)
  have a2 := hs (.x2, .caller 5 0) (by simp)
  change u.gpr .x2 = L.scr + 0#64 at a2
  rw [BitVec.add_zero] at a2
  refine WP.mono (reduce_call hu hL hd ⟨a0, a1, a2⟩) fun t ⟨ht, hf, hp⟩ => ⟨ht, ?_, ?_⟩
  · rw [hm] at hf; exact hf
  · rw [hm] at hp; exact hp

end VG.Proof.Ed25519.AArch64.SignCached
