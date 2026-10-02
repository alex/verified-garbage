import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyMessage.CTCommon

namespace VG.Proof.Ed25519.AArch64.VerifyMessage
open VG VG.AArch64
variable {L : Lay} {t : State}

def init_ready (h0 : t.gpr .x0=L.scr) :
    Whole.CallReady (Proof.Sha512.initAArch64 Spec.Sha512.H0_512) L.E L.inputs L.outputs t :=
  ⟨[],Whole.initWr L.scr,Whole.init_pre h0,
    Whole.covers_writes (Whole.init_writes (by simp [Lay.outputs])),
    Whole.init_writes (by simp [Lay.outputs])⟩

def update_ready (hL : L.Ok) (hsp : t.sp = L.E) {p len : Addr} (h0 : t.gpr .x0=L.scr) (h2 : t.gpr .x2=p)
    (h3 : t.gpr .x3=len) (h4 : t.gpr .x4=L.scr+192)
    (hd : Region.Disjoint ⟨p,len.toNat⟩ L.SCR)
    (hi : ∃ R ∈ L.inputs, Whole.Within ⟨p,len.toNat⟩ R) :
    Whole.CallReady Proof.Sha512.updateAArch64 L.E L.inputs L.outputs t := by
  refine ⟨Whole.updateRd p len,Whole.hashWr L.scr,Whole.update_pre h0 h2 h3 h4 hd (by rw [hsp]; exact hL.e16)
    (by rw [hsp]; exact hL.cc) (by rw [hsp]; exact hL.ck_within hi),?_,hash_writes⟩
  apply covers
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · rw [List.mem_singleton.mp hr]
    obtain ⟨R,hR,hs⟩ := hi
    exact .inr ⟨R,List.mem_append_left _ hR,hs⟩
  · rcases hash_writes r hr with hf | ⟨R,hR,hs⟩
    · exact .inl hf
    · exact .inr ⟨R,List.mem_append_right _ hR,hs⟩

def finalize_ready (hL : L.Ok) (hsp : t.sp = L.E) (h0 : t.gpr .x0=L.scr)
    (h2 : t.gpr .x2=L.E+192) (h3 : t.gpr .x3=L.scr+192) :
    Whole.CallReady Proof.Sha512.finalizeAArch64 L.E L.inputs L.outputs t :=
  ⟨[],Whole.finalizeWr L.scr (L.E+192),Whole.finalize_pre h0 h2 h3
    (hL.kc.sub_left (Offset.sub_base _ (by decide))) (by rw [hsp]; exact hL.e16) (by rw [hsp]; exact hL.cc)
    (by rw [hsp]; exact Whole.ck_frame (by decide : 192 + 64 ≤ 304)),
    Whole.covers_writes finalize_writes,finalize_writes⟩

def reduce_ready (hL : L.Ok) (ha : ReduceArgs L 128 t) :
    Whole.CallReady scalarReduceLocal L.E L.inputs L.outputs t := by
  refine ⟨reduceRd L,reduceWr L 128,reduce_pre hL ha,?_,?_⟩
  · apply covers
    simp only [reduceRd,reduceWr,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl | rfl)
    · exact .inl (digestWithin L)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (scratch_covered L)
  · apply writes
    simp only [reduceWr,List.mem_cons,List.not_mem_nil,or_false]
    rintro r (rfl | rfl)
    · exact .inl (fieldWithin L (by decide))
    · exact .inr (scratchWithin L)

def equation_ready (hL : L.Ok) (ha : EqArgs L t) :
    Whole.CallReady verifyLocal L.E L.inputs L.outputs t :=
  ⟨equationRd L,equationWr L,equation_pre hL ha,equation_covers,equation_writes⟩

end VG.Proof.Ed25519.AArch64.VerifyMessage
