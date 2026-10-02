import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Hash

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64

abbrev SHA (scr : Addr) : Region := ⟨scr, 192⟩
abbrev WORK (scr : Addr) : Region := ⟨scr + 192, 224⟩
def initWr (scr : Addr) : List Region := [SHA scr]
def updateRd (p len : Addr) : List Region := [⟨p, len.toNat⟩]
def hashWr (scr : Addr) : List Region := [SHA scr, WORK scr]
def finalizeWr (scr out : Addr) : List Region := [SHA scr, ⟨out, 64⟩, WORK scr]

theorem sha_sub (scr : Addr) : Region.Sub (SHA scr) ⟨scr, 8192⟩ := Region.sub_prefix (by decide)
theorem work_sub (scr : Addr) : Region.Sub (WORK scr) ⟨scr, 8192⟩ :=
  Offset.sub_base _ (by decide)
theorem sha_work (scr : Addr) : (SHA scr).Disjoint (WORK scr) :=
  Offset.base_disjoint _ (by decide) (by decide)

theorem init_pre {t : State} {scr : Addr} (ha : t.gpr .x0 = scr) :
    (Proof.Sha512.initAArch64 Spec.Sha512.H0_512).pre
      (t.callEntry.withRegions [] (initWr scr)) := by
  simp only [Proof.Sha512.initAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs), ha]
  exact ⟨True.intro, rfl⟩

theorem update_pre {t : State} {scr p len : Addr}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = p) (h3 : t.gpr .x3 = len)
    (h4 : t.gpr .x4 = scr + 192)
    (hd : Region.Disjoint ⟨p, len.toNat⟩ ⟨scr, 8192⟩) (hsp : 16 ≤ t.sp.toNat)
    (hks : (CK t.sp).Disjoint ⟨scr, 8192⟩) (hkp : (CK t.sp).Disjoint ⟨p, len.toNat⟩) :
    Proof.Sha512.updateAArch64.pre
      (t.callEntry.withRegions (updateRd p len) (hashWr scr)) := by
  simp only [Proof.Sha512.updateAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), h0, h2, h3, h4]
  exact ⟨rfl, rfl, sha_work scr, hd.sub_right (sha_sub scr), hd.sub_right (work_sub scr), hsp,
    hks.sub_right (sha_sub scr), hkp, hks.sub_right (work_sub scr)⟩

theorem finalize_pre {t : State} {scr out : Addr}
    (h0 : t.gpr .x0 = scr) (h2 : t.gpr .x2 = out) (h3 : t.gpr .x3 = scr + 192)
    (hd : Region.Disjoint ⟨out, 64⟩ ⟨scr, 8192⟩) (hsp : 16 ≤ t.sp.toNat)
    (hks : (CK t.sp).Disjoint ⟨scr, 8192⟩) (hko : (CK t.sp).Disjoint ⟨out, 64⟩) :
    Proof.Sha512.finalizeAArch64.pre
      (t.callEntry.withRegions [] (finalizeWr scr out)) := by
  simp only [Proof.Sha512.finalizeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp,
    State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs), h0, h2, h3]
  exact ⟨True.intro, rfl, (hd.sub_right (sha_sub scr)).symm, sha_work scr, hd.sub_right (work_sub scr), hsp,
    hks.sub_right (sha_sub scr), hko, hks.sub_right (work_sub scr)⟩

/-- The SHA state and temporary workspace are prefixes of the outer scratch. -/
theorem hash_writes {E scr : Addr} {wr : List Region} (hs : (⟨scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ hashWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  simp only [hashWr, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_, hs, 0, (BitVec.add_zero scr).symm, by change 0+192≤8192; decide⟩
  · exact .inr ⟨_, hs, 192, rfl, by change 192+224≤8192; decide⟩

theorem init_writes {E scr : Addr} {wr : List Region} (hs : (⟨scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ initWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  simp only [initWr, List.mem_singleton] at hr
  subst r
  exact .inr ⟨_, hs, 0, (BitVec.add_zero scr).symm, by change 0+192≤8192; decide⟩

theorem covers_writes {E : Addr} {rd wr ws : List Region}
    (hw : ∀ r ∈ ws, Within r (FR E) ∨ ∃ R ∈ wr, Within r R) :
    Covers ws (rd ++ FR E :: wr) := by
  refine Covers.of_sub fun r hr => ?_
  rcases hw r hr with hf | ⟨R, hR, hs⟩
  · exact ⟨FR E, List.mem_append_right _ List.mem_cons_self, hf⟩
  · exact ⟨R, List.mem_append_right _ (List.mem_cons_of_mem _ hR), hs⟩

end VG.Proof.Ed25519.AArch64.Whole
