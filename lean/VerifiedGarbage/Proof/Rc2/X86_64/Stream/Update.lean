import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Long

/-! # Streaming RC2-CBC on x86-64: the update functions -/

set_option linter.unusedSimpArgs false
namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.WriteBytes VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def cbcName : Spec.Rc2.Direction → String
  | .encrypt => "vg_rc2_cbc_encrypt"
  | .decrypt => "vg_rc2_cbc_decrypt"

theorem cbcCall_eq (d : Spec.Rc2.Direction) : cbcCall d = .call (cbcName d) (Cbc.cbc d) := by
  cases d <;> rfl

theorem cbc_correct (d : Spec.Rc2.Direction) (s : State) (hs : (Cbc.contract d).pre s) :
    ∃ t s', Exec isa (Cbc.cbc d) s t s' ∧ abiPreserved s s' ∧ (Cbc.contract d).post s s' := by
  cases d
  · exact Cbc.encrypt_correct s hs
  · exact Cbc.decrypt_correct s hs

theorem cbc_noSp (d : Spec.Rc2.Direction) : NoSp (Cbc.cbc d) := by
  have h : ((instrs (Cbc.cbc d)).all fun i => !Taint.clobbers i .rsp) = true := by
    cases d
    · change ((instrs Cbc.encrypt).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
    · change ((instrs Cbc.decrypt).all _) = true
      rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem cbc_depth (d : Spec.Rc2.Direction) : (Cbc.cbc d).depth = 1 := by
  cases d <;> rfl

/-- The call of the CBC function, and the update's postcondition. -/
theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (s.gpr .r9).toNat ≠ 0) (t : State) (ht : Mid s t) :
    WP isa (cbcCall d) t (fun s' => ((∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧
      s'.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64) ∧
      (Spec.Rc2.contextAt s'.mem (s.gpr .rdi) d (((s.gpr .rsi).toNat + (s.gpr .rcx).toNat) % 8) =
        (Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
          (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)).1 ∧
      Spec.Rc2.bytesAt s'.mem (s.gpr .r8) (s.gpr .r9).toNat =
        (Spec.Rc2.update (Spec.Rc2.contextAt s.mem (s.gpr .rdi) d (s.gpr .rsi).toNat)
          (Spec.Rc2.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)).2)) := by
  obtain ⟨hsp, _, hrd, hwr, ctxData, ctxOut, ctxBuf, _, dataOut, _, outBuf, _, _, retCtx, _, retOut, retBuf, _,
    stCtx, _, stOut, stBuf, _, _, _, fitOut, _, hp, hN⟩ := hs
  obtain ⟨rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, callee₁, rd₁, wr₁, frame₁, out₁, pend₁⟩ := ht
  generalize hC : s.gpr .rdi = C at *
  generalize hP : (s.gpr .rsi).toNat = P at *
  generalize hA : s.gpr .rdx = A at *
  generalize hL : (s.gpr .rcx).toNat = L at *
  generalize hO : s.gpr .r8 = O at *
  generalize hNN : (s.gpr .r9).toNat = N at *
  generalize hB : stackArg s 0 = B at *
  generalize hSP : s.gpr .rsp = SP at *
  have h8 : 8 ≤ N := by omega
  have hNN8 : 8 * (N / 8) = N := by omega
  have e128 : C + 128 = C + BitVec.ofNat 64 128 := rfl
  have e136 : C + 136 = C + BitVec.ofNat 64 136 := rfl
  have stackSub : Region.Sub (below (SP - 8) 8) (below SP 16) := below_callee _ _
  have retSub : Region.Sub ⟨SP - 8, 8⟩ (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  have ivSub : Region.Sub ⟨C + BitVec.ofNat 64 128, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  have keySub : Region.Sub ⟨C, 128⟩ ⟨C, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨B, 512⟩ ⟨B, 576⟩ := Region.sub_prefix (by decide)
  rw [cbcCall_eq]
  refine WP.call (k := Cbc.contract d) (cbc_correct d) (cbc_noSp d) (by rw [cbc_depth]; decide)
    (rd := [⟨C, 128⟩]) (wr := [⟨C + 128, 8⟩, ⟨O, 8 * (N / 8)⟩, ⟨B, 512⟩]) ?_ ?_ ?_ ?_
  · simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      rdi₁, rsi₁, rdx₁, rcx₁, r8₁, rsp₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N / 8 < 2 ^ 64 by omega),
      hNN8, e128]
    refine ⟨trivial, trivial, Offset.base_disjoint _ (by decide) (by decide), ctxOut.sub_left keySub,
      (ctxBuf.sub_left keySub).sub_right bufSub, ctxOut.sub_left ivSub, (ctxBuf.sub_left ivSub).sub_right bufSub,
      outBuf.sub_right bufSub, (stCtx.sub_left retSub).sub_right ivSub, stOut.sub_left retSub,
      (stBuf.sub_left retSub).sub_right bufSub, (stCtx.sub_left stackSub).sub_right keySub,
      (stCtx.sub_left stackSub).sub_right ivSub, stOut.sub_left stackSub,
      (stBuf.sub_left stackSub).sub_right bufSub, fitOut⟩
  · rw [rd₁, wr₁, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, by simp, by simp only [hNN8]; omega⟩
    · exact ⟨⟨B, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [wr₁, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨C, 144⟩, by simp, 128, rfl, by simp⟩
    · exact ⟨⟨O, N⟩, by simp, 0, by simp, by simp only [hNN8]; omega⟩
    · exact ⟨⟨B, 576⟩, by simp, 0, by simp, by simp⟩
  intro s' rd' wr' callee' frame' _ ⟨s₂, mem₂, _, post₂⟩
  rw [cbc_depth, rsp₁, hNN8, e128] at frame'
  -- What the call leaves.
  have stackFrame : Frame [below SP 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, rsp₁]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
  have stack8 : Region.Sub (below SP 8) (below SP 16) := Offset.sub_below SP (by decide) (by decide)
  simp only [Cbc.contract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    rdi₁, rsi₁, rdx₁, rcx₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show N / 8 < 2 ^ 64 by omega), mem₂] at post₂
  rw [scheduleAt_frame stackFrame C (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ((stCtx.sub_left stack8).sub_right keySub).symm),
    blockAt_frame stackFrame (C + 128) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [e128]; exact ((stCtx.sub_left stack8).sub_right ivSub).symm),
    blocksAt_frame stackFrame O (N / 8) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hNN8]; exact (stOut.sub_left stack8).symm)] at post₂
  -- Regions the call leaves alone.
  have callSep (R : Region) (hiv : R.Disjoint ⟨C + BitVec.ofNat 64 128, 8⟩) (hout : R.Disjoint ⟨O, N⟩)
      (hbuf : R.Disjoint ⟨B, 576⟩) (hst : R.Disjoint (below SP 16)) :
      ∀ r ∈ [(⟨C + BitVec.ofNat 64 128, 8⟩ : Region), ⟨O, N⟩, ⟨B, 512⟩] ++ [below SP 16], R.Disjoint r := by
    intro r hr
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hiv
    · exact hout
    · exact hbuf.sub_right bufSub
    · exact hst
  have midSep (R : Region) (hout : R.Disjoint ⟨O, N⟩) (hpend : R.Disjoint ⟨C + BitVec.ofNat 64 136, 8⟩) :
      ∀ r ∈ [(⟨O, N⟩ : Region), ⟨C + BitVec.ofNat 64 136, 8⟩], R.Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hout
    · exact hpend
  have pendSub : Region.Sub ⟨C + BitVec.ofNat 64 136, 8⟩ ⟨C, 144⟩ := Offset.sub_base _ (by decide)
  refine ⟨⟨fun r hr => (callee' r hr).trans (callee₁ r hr), ?_⟩, ?_⟩
  · rw [frame'.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (callSep _ (retCtx.sub_right ivSub) retOut
        retBuf (Offset.base_disjoint_below _ (by decide))) (by decide),
      frame₁.readW (r := ⟨SP, 8⟩) (Region.contains_self _ _) (midSep _ retOut (retCtx.sub_right pendSub))
        (by decide)]
  · rw [hN] at out₁ pend₁ post₂ ⊢
    rw [Nat.mul_div_cancel _ (by decide : 0 < 8)] at post₂
    have keyMid := scheduleAt_frame frame₁ C (midSep _ (ctxOut.sub_left keySub)
      (Offset.base_disjoint _ (by decide) (by decide)))
    refine update_post_long hp (by omega) out₁ keyMid ?_ ?_ ?_ post₂.1 post₂.2
    · rw [e128]
      exact blockAt_frame frame₁ _ (midSep _ (ctxOut.sub_left ivSub) (Offset.disjoint _ (by decide) (by decide) (by decide)))
    · rw [e136, Proof.Rc2.bytesAt_frame frame' _ _ (by omega) (callSep _
          (Offset.disjoint _ (by omega) (by omega) (by decide)) (ctxOut.sub_left (Offset.sub_base _ (by omega)))
          (ctxBuf.sub_left (Offset.sub_base _ (by omega))) (stCtx.symm.sub_left (Offset.sub_base _ (by omega)))),
        ← e136, pend₁]
    · exact scheduleAt_frame frame' C (callSep _ (Offset.base_disjoint _ (by decide) (by decide))
        (ctxOut.sub_left keySub) (ctxBuf.sub_left keySub) (stCtx.symm.sub_left keySub))

end VG.Proof.Rc2.X86_64.Stream
