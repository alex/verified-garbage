import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTCommon

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm
variable {L : Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 184) (ha : ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
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
    · exact .inr (.inr (scratchWithin L))
  exact ⟨reduceRd L, reduceWr L d, reduce_pre hL hd ha, cov, ws⟩

def base_ready (hL : L.Ok) (ha : BaseArgs L s) : Whole.CallReady scalarBaseLocal L.E L.inputs L.outputs s := by
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
  exact ⟨baseRd L, baseWr L, base_pre hL ha, cov, ws⟩

def mul_ready {g m} (hc : Ctx L g m s) (hL : L.Ok) (ha : MulArgs L s) : Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
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
  exact ⟨mulRd L, mulWr L, mul_pre hc hL ha, cov, ws⟩

def init_ready (hL : L.Ok) (ha : s.gpr .r0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initArm Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha hL.nc, Whole.covers_writes hw, hw⟩

def update_ready (hL : L.Ok) (he : s.sp = L.E) {count p len : BitVec 32}
    (hi : Input L p len) (ha : UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateArm L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd L.E p len, Whole.hashWr L.scr, update_pre hL he ha hi, update_covers hi, hw⟩

def finalize_ready (hL : L.Ok) (he : s.sp = L.E) {count : BitVec 32} (ha : FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeArm L.E L.inputs L.outputs s :=
  ⟨Whole.finalizeRd L.E, Whole.finalizeWr L.scr (L.E + 184), finalize_pre hL he ha,
    finalize_covers hL, final_writes hL⟩

end VG.Proof.Ed25519.Arm.SignCached
