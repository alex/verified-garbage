import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTCommon

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64
variable {L : Lay} {s : State}

def reduce_ready (hL : L.Ok) {d : Nat} (hd : d + 32 ≤ 256) (ha : ReduceArgs L d s) : Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs s := by
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
  exact ⟨reduceRd L, reduceWr L d, reduce_pre hL ha, cov, ws⟩

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

def mul_ready (hL : L.Ok) (ha : MulArgs L s) : Whole.CallReady scalarMulAddLocal L.E L.inputs L.outputs s := by
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
  exact ⟨mulRd L, mulWr L, mul_pre hL ha, cov, ws⟩

def init_ready (ha : s.gpr .x0 = L.scr) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs s := by
  have hw := Whole.init_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨[], Whole.initWr L.scr, Whole.init_pre ha, Whole.covers_writes hw, hw⟩

def UpdateArgs (L : Lay) (count p len : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = p ∧ s.gpr .x3 = len ∧ s.gpr .x4 = L.scr + 192

def update_ready (hL : L.Ok) (hsp : s.sp = L.E) {count p len : Addr} (hi : Input L p len)
    (ha : UpdateArgs L count p len s) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs s := by
  have hw := Whole.hash_writes (E := L.E) (wr := L.outputs) (by simp [Lay.outputs] : L.SCR ∈ L.outputs)
  exact ⟨Whole.updateRd p len, Whole.hashWr L.scr,
    Whole.update_pre ha.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 hi.scratch (by rw [hsp]; exact hL.e16)
      (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hi.ck hL), update_covers hi, hw⟩

def FinalArgs (L : Lay) (count : Addr) (s : State) : Prop :=
  s.gpr .x0 = L.scr ∧ s.gpr .x1 = count ∧ s.gpr .x2 = L.E + 192 ∧ s.gpr .x3 = L.scr + 192

def finalize_ready (hL : L.Ok) (hsp : s.sp = L.E) {count : Addr} (ha : FinalArgs L count s) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs s :=
  ⟨[], Whole.finalizeWr L.scr (L.E + 192),
    Whole.finalize_pre ha.1 ha.2.2.1 ha.2.2.2 (hL.kc.sub_left (digestWithin L).sub)
      (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
      (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes (final_writes L), final_writes L⟩

end VG.Proof.Ed25519.AArch64.SignCached
