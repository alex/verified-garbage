import VerifiedGarbage.Proof.Ed25519.Arm.Whole.Hash

namespace VG.Proof.Ed25519.Arm.Whole
open VG VG.Arm

abbrev SHA (scr : BitVec 32) : Region := ⟨State.addr scr,192⟩
abbrev WORK (scr : BitVec 32) : Region := ⟨State.addr scr+192,272⟩
abbrev CALLARGS (E : BitVec 32) (n : Nat) : Region := ⟨State.addr E,n⟩
def initWr (scr : BitVec 32) : List Region := [SHA scr]
def updateRd (E p len : BitVec 32) : List Region := [⟨State.addr p,len.toNat⟩,CALLARGS E 12]
def hashWr (scr : BitVec 32) : List Region := [SHA scr,WORK scr]
def finalizeRd (E : BitVec 32) : List Region := [CALLARGS E 8]
def finalizeWr (scr out : BitVec 32) : List Region := [SHA scr,⟨State.addr out,64⟩,WORK scr]

theorem sha_sub (scr : BitVec 32) : Region.Sub (SHA scr) ⟨State.addr scr,8192⟩ := Region.sub_prefix (by decide)
theorem work_sub (scr : BitVec 32) : Region.Sub (WORK scr) ⟨State.addr scr,8192⟩ := Offset.sub_base _ (by decide)
theorem sha_work (scr : BitVec 32) : (SHA scr).Disjoint (WORK scr) := Offset.base_disjoint _ (by decide) (by decide)

theorem init_pre {t : State} {scr : BitVec 32} (ha : t.gpr .r0 = scr)
    (hn : scr.toNat+8192 ≤ 2^32) :
    (Proof.Sha512.initArm Spec.Sha512.H0_512).pre (t.callEntry.withRegions [] (initWr scr)) := by
  simp only [Proof.Sha512.initArm,State.withRegions_rd,State.withRegions_wr,
    State.withRegions_gpr,State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),ha]
  exact ⟨True.intro,rfl,by omega⟩

theorem update_pre {t : State} {E scr p len : BitVec 32}
    (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (hdp : stackArg t 0 = p) (hl : stackArg t 1 = len) (hw : stackArg t 2 = scr+192)
    (hd : Region.Disjoint ⟨State.addr p,len.toNat⟩ ⟨State.addr scr,8192⟩)
    (hs : (CALLARGS E 12).Disjoint ⟨State.addr scr,8192⟩)
    (nc : scr.toNat+8192 ≤ 2^32) (np : p.toNat+len.toNat ≤ 2^32) (ne : E.toNat+12 ≤ 2^32) :
    Proof.Sha512.updateArm.pre (t.callEntry.withRegions (updateRd E p len) (hashWr scr)) := by
  have ac : State.addr (scr+192) = State.addr scr+192 := addr_add (k := 192) (by omega)
  have wc : (scr+192).toNat+272 ≤ 2^32 := by
    rw [BitVec.toNat_add_of_lt (by change scr.toNat+192<2^32; omega)]
    change scr.toNat+192+272≤2^32
    omega
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (updateRd E p len) (hashWr scr)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (updateRd E p len) (hashWr scr)) 0 = State.addr t.sp := by simp [stackArgAddr,State.withRegions_sp,State.callEntry_sp]
  simp only [Proof.Sha512.updateArm,sa,spa,State.withRegions_rd,State.withRegions_wr,
    State.withRegions_gpr,State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),h0,
    State.withRegions_sp,State.callEntry_sp]
  rw [hdp,hl,hw,he,ac]
  exact ⟨rfl,rfl,sha_work scr,hd.sub_right (sha_sub scr),hd.sub_right (work_sub scr),
    hs.sub_right (sha_sub scr),hs.sub_right (work_sub scr),by omega,np,wc,ne⟩

theorem finalize_pre {t : State} {E scr out : BitVec 32}
    (he : t.sp = E) (h0 : t.gpr .r0 = scr)
    (ho : stackArg t 0 = out) (hw : stackArg t 1 = scr+192)
    (hd : Region.Disjoint ⟨State.addr out,64⟩ ⟨State.addr scr,8192⟩)
    (hs : (CALLARGS E 8).Disjoint ⟨State.addr scr,8192⟩)
    (hso : (CALLARGS E 8).Disjoint ⟨State.addr out,64⟩)
    (nc : scr.toNat+8192 ≤ 2^32) (no : out.toNat+64 ≤ 2^32) (ne : E.toNat+8 ≤ 2^32) :
    Proof.Sha512.finalizeArm.pre (t.callEntry.withRegions (finalizeRd E) (finalizeWr scr out)) := by
  have ac : State.addr (scr+192) = State.addr scr+192 := addr_add (k := 192) (by omega)
  have wc : (scr+192).toNat+272 ≤ 2^32 := by
    rw [BitVec.toNat_add_of_lt (by change scr.toNat+192<2^32; omega)]
    change scr.toNat+192+272≤2^32
    omega
  have sa (j : Nat) : stackArg (t.callEntry.withRegions (finalizeRd E) (finalizeWr scr out)) j = stackArg t j := rfl
  have spa : stackArgAddr (t.callEntry.withRegions (finalizeRd E) (finalizeWr scr out)) 0 = State.addr t.sp := by simp [stackArgAddr,State.withRegions_sp,State.callEntry_sp]
  simp only [Proof.Sha512.finalizeArm,sa,spa,State.withRegions_rd,State.withRegions_wr,
    State.withRegions_gpr,State.callEntry_gpr _ (by decide : Reg.r0 ∉ linkRegs),h0,
    State.withRegions_sp,State.callEntry_sp]
  rw [ho,hw,he,ac]
  exact ⟨rfl,rfl,(hd.sub_right (sha_sub scr)).symm,sha_work scr,hd.sub_right (work_sub scr),
    hs.sub_right (sha_sub scr),hso,hs.sub_right (work_sub scr),by omega,no,wc,ne⟩

/-- Hash calls only write prefixes of the outer scratch allocation. -/
theorem hash_writes {E scr : BitVec 32} {wr : List Region} (hs : (⟨State.addr scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ hashWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  simp only [hashWr,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact .inr ⟨_,hs,0,(BitVec.add_zero _).symm,by change 0+192≤8192; decide⟩
  · exact .inr ⟨_,hs,192,rfl,by change 192+272≤8192; decide⟩

theorem init_writes {E scr : BitVec 32} {wr : List Region} (hs : (⟨State.addr scr,8192⟩ : Region) ∈ wr) :
    ∀ r ∈ initWr scr, Within r (FR E) ∨ ∃ R ∈ wr, Within r R := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact .inr ⟨_,hs,0,(BitVec.add_zero _).symm,by change 0+192≤8192; decide⟩

theorem covers_writes {E : BitVec 32} {rd wr ws : List Region}
    (hw : ∀ r ∈ ws, Within r (FR E) ∨ ∃ R ∈ wr, Within r R) : Covers ws (rd++FR E::wr) := by
  refine Covers.of_sub fun r hr => ?_
  rcases hw r hr with hf | ⟨R,hR,hs⟩
  · exact ⟨FR E,List.mem_append_right _ List.mem_cons_self,hf⟩
  · exact ⟨R,List.mem_append_right _ (List.mem_cons_of_mem _ hR),hs⟩

end VG.Proof.Ed25519.Arm.Whole
