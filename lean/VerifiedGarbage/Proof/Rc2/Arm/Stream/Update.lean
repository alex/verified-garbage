import VerifiedGarbage.Proof.Rc2.Arm.Stream.Long

/-! # Streaming RC2-CBC on ARMv7: the update functions

Without a complete block, the data is appended to the pending bytes
(`short_ok`); otherwise, after the copies (`long_ok`), the CBC function runs
on `out` and `lr` is restored (`call_ok`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.WriteBytes VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_add wp_ldr wp_ldrSp wp_cmp eval_eq cmp0)

/-- The postcondition of `update`: the callee-saved registers and the contract's. -/
abbrev UpdPost (d : Spec.Rc2.Direction) (s s' : State) : Prop :=
  (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ (updateContract d).post s s'

/-- With `out_len = 0` (so `pending_len + len < 8`). -/
theorem short_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hz : (stackArg s 1).toNat = 0) (t : State) (ht : Keep s t) :
    WP isa short t (UpdPost d s) := by
  obtain ⟨_, _, hrd, hwr, ctxData, _, _, _, _, _, _, _, _, _, _, _, _, _, fitC, fitD, _, _, hp, hN⟩ := hs
  have hshort : (s.gpr .r1).toNat + (s.gpr .r3).toNat < 8 := by omega
  have hNlt := (s.gpr .r3).isLt
  rw [short]
  refine WP.seq (wp_add (op2_reg _ _) fun t₁ u₁ => WP.block_nil ?_)
  have g₁ (r : Reg) (h₁ : r ≠ .r12) (h₂ : r ≠ .r1) : t₁.gpr r = s.gpr r := by
    rw [u₁.other _ h₂, ht.reg _ h₁]
  have r1₁ : t₁.gpr .r1 = s.gpr .r0 + BitVec.ofNat 32 (s.gpr .r1).toNat := by
    rw [u₁.gpr, ht.reg _ (by decide), ht.reg _ (by decide), ← ofNat_toNat32]
  have hD : State.addr (t₁.gpr .r1) + BitVec.ofNat 64 136 =
      State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat) := by
    rw [r1₁, addr_add (by omega), Offset.add_add, Nat.add_comm]
  have dstSub : Region.Sub ⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat), (s.gpr .r3).toNat⟩
      ⟨State.addr (s.gpr .r0), 144⟩ := Offset.sub_base _ (by omega)
  apply WP.mono (copy_ok (s := t₁) (src := .r2) (dst := .r1) (cnt := .r3) (so := 0) (dd := 136)
    (L := (s.gpr .r3).toNat) (A := State.addr (s.gpr .r2))
    (B := State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [g₁ _ (by decide) (by decide)]; exact ofNat_toNat32 _) hNlt
    (by rw [g₁ _ (by decide) (by decide)]; omega)
    (by rw [r1₁, toNat_add32 (by omega)]; omega)
    (by rw [g₁ _ (by decide) (by decide)]; exact add0 _) hD
    (fun _ => by
      rw [u₁.rd, u₁.wr, ht.rd, ht.wr, ← add0 (State.addr (s.gpr .r2))]
      exact cov1 (len := (s.gpr .r3).toNat) (by rw [hrd]; simp) (by omega))
    (fun _ => by rw [u₁.wr, ht.wr]; exact cov1 (len := 144) (by rw [hwr]; simp) (by omega))
    (fun _ => ctxData.symm.sub_right dstSub))
  intro s' c'
  have m' : s'.mem = writeBytes s.mem (State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat))
      (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) := by
    rw [← ht.mem, ← u₁.mem]; exact c'.mem
  have frame : Frame [⟨State.addr (s.gpr .r0) + BitVec.ofNat 64 (136 + (s.gpr .r1).toNat), (s.gpr .r3).toNat⟩]
      s.mem s'.mem := by
    rw [m']; exact writeBytes_frame' _ _ _ (Proof.Rc2.bytesAt_length _ _ _)
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [c'.keep _ (by decide) (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide)]
    · obtain ⟨_, h1, h2, h3, h12⟩ := preserved_ne hr hl
      rw [c'.keep _ h2 h1 h3 h12, g₁ _ h12 h1]
  · show Spec.Rc2.contextAt s'.mem _ d _ = _ ∧ _
    rw [hN]
    refine update_post_short hshort ?_ ?_ ?_
    · exact Proof.Rc2.scheduleAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.base_disjoint _ (by omega) (by omega))
    · rw [e128]
      exact Proof.Rc2.blockAt_frame frame _ (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact Offset.disjoint _ (by omega) (by omega) (by omega))
    · rw [e136, Proof.Rc2.bytesAt_add, Offset.add_add,
        Proof.Rc2.bytesAt_frame frame _ _ (by omega) (fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact Offset.disjoint _ (by omega) (by omega) (by omega)),
        m', bytesAt_writeBytes_self _ _ (Proof.Rc2.bytesAt_length _ _ _) (by omega)]

/-- Regions the call leaves alone. -/
theorem callSep {C O S : BitVec 32} {OL : Nat} {sp : Addr} (R : Region)
    (hiv : R.Disjoint ⟨State.addr C + BitVec.ofNat 64 128, 8⟩)
    (hout : R.Disjoint ⟨State.addr O, OL⟩) (hbuf : R.Disjoint ⟨State.addr S, 512⟩)
    (hst : R.Disjoint ⟨sp, 8⟩) :
    ∀ r ∈ [(⟨State.addr C + BitVec.ofNat 64 128, 8⟩ : Region), ⟨State.addr O, OL⟩, ⟨State.addr S, 512⟩,
      ⟨sp, 8⟩], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hiv
  · exact hout
  · exact hbuf
  · exact hst

/-- Regions the copies leave alone. -/
theorem midSep {C O S : BitVec 32} {OL : Nat} (R : Region) (hout : R.Disjoint ⟨State.addr O, OL⟩)
    (hpend : R.Disjoint ⟨State.addr C + BitVec.ofNat 64 136, 8⟩)
    (hlr : R.Disjoint ⟨State.addr S + BitVec.ofNat 64 512, 4⟩) :
    ∀ r ∈ [(⟨State.addr O, OL⟩ : Region), ⟨State.addr C + BitVec.ofNat 64 136, 8⟩,
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], R.Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hout
  · exact hpend
  · exact hlr

theorem ivSub (C : BitVec 32) : Region.Sub ⟨State.addr C + BitVec.ofNat 64 128, 8⟩ ⟨State.addr C, 144⟩ :=
  Offset.sub_base _ (by decide)
theorem keySub (C : BitVec 32) : Region.Sub ⟨State.addr C, 128⟩ ⟨State.addr C, 144⟩ :=
  Region.sub_prefix (by decide)
theorem pendSub (C : BitVec 32) : Region.Sub ⟨State.addr C + BitVec.ofNat 64 136, 8⟩ ⟨State.addr C, 144⟩ :=
  Offset.sub_base _ (by decide)
theorem bufSub (S : BitVec 32) : Region.Sub ⟨State.addr S, 512⟩ ⟨State.addr S, 576⟩ :=
  Region.sub_prefix (by decide)
theorem lrSub (S : BitVec 32) : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ :=
  Offset.sub_base _ (by decide)

theorem eN {OL : Nat} (h8 : OL % 8 = 0) (hOL : OL < 2 ^ 32) : 8 * (BitVec.ofNat 32 (OL / 8)).toNat = OL := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem eI {C : BitVec 32} (h : C.toNat + 144 ≤ 2 ^ 32) :
    State.addr (C + 128) = State.addr C + BitVec.ofNat 64 128 := addr_add (k := 128) (by omega)

/-- The arguments of the CBC function. -/
theorem mid_pre (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (t : State) (ht : Mid s t) :
    CbcPre t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0) (BitVec.ofNat 32 ((stackArg s 1).toNat / 8))
      (stackArg s 2) := by
  obtain ⟨sp8, _, _, hwr, _, ctxOut, ctxScr, _, _, _, outScr, _, _, bCtx, _, bOut, bScr, _, fitC, _, fitO,
    fitS, hp, hN⟩ := hs
  have eN' := eN (OL := (stackArg s 1).toNat) (by omega) (stackArg s 1).isLt
  have eI' := eI fitC
  have eb : (⟨State.addr t.sp - 8, 8⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [ht.sp]
  refine ⟨ht.r0, ht.r1, ht.r2, ht.r3, ht.r12, by rw [ht.sp]; exact sp8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by omega, by show (s.gpr .r0 + BitVec.ofNat 32 128).toNat + 8 ≤ _; rw [toNat_add32 (by omega)]; omega,
    by rw [eN']; exact fitO, by omega, ?_, ?_⟩
  · rw [eI']; exact Offset.base_disjoint _ (by decide) (by decide)
  · rw [eN']; exact ctxOut.sub_left (keySub _)
  · exact (ctxScr.sub_left (keySub _)).sub_right (bufSub _)
  · rw [eI', eN']; exact ctxOut.sub_left (ivSub _)
  · rw [eI']; exact (ctxScr.sub_left (ivSub _)).sub_right (bufSub _)
  · rw [eN']; exact outScr.sub_right (bufSub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb]; exact bCtx.sub_right (keySub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb, eI']; exact bCtx.sub_right (ivSub _)
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb, eN']; exact bOut
  · show (Region.mk (State.addr t.sp - 8) 8).Disjoint _; rw [eb]; exact bScr.sub_right (bufSub _)
  · rw [ht.rd, ht.wr, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (s.gpr .r0), 144⟩, by simp, 0, (add0 _).symm, by simp⟩
  · rw [ht.wr, hwr, eI', eN']
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨State.addr (s.gpr .r0), 144⟩, by simp, 128, rfl, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩, by simp, 0, (add0 _).symm, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, 0, (add0 _).symm, by simp⟩

/-- The update's postcondition, from the memory the call leaves. -/
theorem post_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Mid s t) (u : State)
    (hu : CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    (updateContract d).post s u := by
  obtain ⟨_, _, _, _, _, ctxOut, ctxScr, _, _, _, _, _, _, bCtx, _, _, _, _, fitC, _, _, _, hp, hN⟩ := hs
  have frame₁ := ht.frame
  have out₁ := ht.out
  have pend₁ := ht.pend
  obtain ⟨_, _, _, _, frame₂, data₂, iv₂⟩ := hu
  have hOLlt := (stackArg s 1).isLt
  have eb : below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, ht.sp]
  rw [eI fitC, eN (by omega) hOLlt, eb] at frame₂
  rw [eI fitC, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show (stackArg s 1).toNat / 8 < 2 ^ 32 by omega)] at data₂ iv₂
  show Spec.Rc2.contextAt u.mem _ d _ = _ ∧ _
  rw [hN] at out₁ pend₁ data₂ iv₂ frame₁ frame₂ ctxOut ⊢
  rw [Nat.mul_div_cancel _ (by decide : 0 < 8)] at data₂ iv₂
  have keyMid := Proof.Rc2.scheduleAt_frame frame₁ _ (midSep _ (ctxOut.sub_left (keySub _))
    (Offset.base_disjoint _ (by decide) (by decide)) ((ctxScr.sub_left (keySub _)).sub_right (lrSub _)))
  refine update_post_long hp (by omega) out₁ keyMid ?_ ?_ ?_ data₂ iv₂
  · rw [e128]
    exact Proof.Rc2.blockAt_frame frame₁ _ (midSep _ (ctxOut.sub_left (ivSub _))
      (Offset.disjoint _ (by decide) (by decide) (by decide)) ((ctxScr.sub_left (ivSub _)).sub_right (lrSub _)))
  · rw [e136, Proof.Rc2.bytesAt_frame frame₂ _ _ (by omega) (callSep _
        (Offset.disjoint _ (by omega) (by omega) (by decide)) (ctxOut.sub_left (Offset.sub_base _ (by omega)))
        ((ctxScr.sub_left (Offset.sub_base _ (by omega))).sub_right (bufSub _))
        (bCtx.symm.sub_left (Offset.sub_base _ (by omega)))), pend₁]
  · exact Proof.Rc2.scheduleAt_frame frame₂ _ (callSep _ (Offset.base_disjoint _ (by decide) (by decide))
      (ctxOut.sub_left (keySub _)) ((ctxScr.sub_left (keySub _)).sub_right (bufSub _))
      (bCtx.symm.sub_left (keySub _)))

/-- `lr` back from `scratch + 512`, after the call. -/
theorem restore_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Mid s t) (u : State)
    (hu : CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    WP isa (.block restoreLr) u (UpdPost d s) := by
  have hpost := post_ok d s hs hnz t ht u hu
  obtain ⟨_, spfit, hrd, hwr, _, ctxOut, ctxScr, ctxArgs, _, _, outScr, outArgs, scrArgs, bCtx, _, bOut,
    bScr, bArgs, fitC, _, _, fitS, hp, hN⟩ := hs
  have frame₁ := ht.frame
  have lr₁ := ht.lr
  obtain ⟨rd₂, wr₂, sp₂, saved₂, frame₂, _, _⟩ := hu
  have hOLlt := (stackArg s 1).isLt
  have eb : below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, ht.sp]
  rw [eI fitC, eN (by omega) hOLlt, eb] at frame₂
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    argIn (by rw [hrd]; simp) hi spfit
  rw [show restoreLr = [.ldrSp .r12 8, .ldr .lr .r12 512] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [sp₂, ht.sp]; rfl)
    (by rw [rd₂, wr₂, ht.rd, ht.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_
  have hc2 : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 2) (32 / 8) := by
    rw [stackArgAddr_eq s (i := 2) (by decide) spfit]; exact Offset.contains_base _ (by decide) (by decide)
  have argsS : u.mem.readW (stackArgAddr s 2) 32 = stackArg s 2 := by
    rw [frame₂.readW hc2 (callSep _ (ctxArgs.symm.sub_right (ivSub _)) outArgs.symm
        (scrArgs.symm.sub_right (bufSub _)) bArgs.symm) (by decide),
      stackArg_frame frame₁ spfit (midSep _ outArgs.symm (ctxArgs.symm.sub_right (pendSub _))
        (scrArgs.symm.sub_right (lrSub _))) (by decide)]
  refine wp_ldr (a := State.addr (stackArg s 2) + BitVec.ofNat 64 512) (by decide)
    (by rw [v₁.gpr, argsS]; exact addr_add (by omega))
    (by rw [v₁.rd, v₁.wr, rd₂, wr₂, ht.rd, ht.wr, hwr]
        exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₂ v₂ => WP.block_nil ?_
  have lr₂ : u₂.gpr .lr = s.gpr .lr := by
    rw [v₂.gpr, v₁.mem, frame₂.readW (r := ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩)
      (Region.contains_self _ _)
      (callSep _ ((ctxScr.sub_left (ivSub _)).sub_right (lrSub _)).symm (outScr.sub_right (lrSub _)).symm
        (Offset.disjoint_base _ (by decide) (by decide)) (bScr.sub_right (lrSub _)).symm) (by decide), lr₁]
  have mem₂ : u₂.mem = u.mem := by rw [v₂.mem, v₁.mem]
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [lr₂]
    · obtain ⟨_, _, _, _, h12⟩ := preserved_ne hr hl
      rw [v₂.other _ hl, v₁.other _ h12, saved₂ r hr hl, ht.callee r hr hl]
  · show Spec.Rc2.contextAt u₂.mem _ d _ = _ ∧ Spec.Rc2.bytesAt u₂.mem _ _ = _
    rw [mem₂]; exact hpost

/-- The call of the CBC function, `lr` restored, and the update's postcondition. -/
theorem call_ok (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (hnz : (stackArg s 1).toNat ≠ 0) (t : State) (ht : Mid s t) :
    WP isa (.seq (cbcCall d) (.block restoreLr)) t (UpdPost d s) :=
  WP.seq (WP.mono (cbc_call (d := d) (mid_pre d s hs t ht)) fun u hu => restore_ok d s hs hnz t ht u hu)

/-- The stack arguments after the call are those on entry. -/
theorem args_after (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s)
    (t : State) (ht : Mid s t) (u : State)
    (hu : CbcPost d t (s.gpr .r0) (s.gpr .r0 + 128) (stackArg s 0)
      (BitVec.ofNat 32 ((stackArg s 1).toNat / 8)) (stackArg s 2) u) :
    ∀ i < 3, stackArg u i = stackArg s i := by
  obtain ⟨_, spfit, _, _, _, _, _, ctxArgs, _, _, _, outArgs, scrArgs, _, _, _, _, bArgs, fitC, _, _, _, hp,
    hN⟩ := hs
  have frame₂ := hu.frame
  have hOLlt := (stackArg s 1).isLt
  have eb : below t = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, ht.sp]
  rw [eI fitC, eN (by omega) hOLlt, eb] at frame₂
  intro i hi
  have hc : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s i) (32 / 8) := by
    rw [stackArgAddr_eq s hi spfit]; exact Offset.contains_base _ (by omega) (by omega)
  have ea : stackArgAddr u i = stackArgAddr s i := by unfold stackArgAddr; rw [hu.sp, ht.sp]
  rw [stackArg, ea, frame₂.readW hc (callSep _ (ctxArgs.symm.sub_right (ivSub _)) outArgs.symm
      (scrArgs.symm.sub_right (bufSub _)) bArgs.symm) (by decide),
    stackArg_frame ht.frame spfit (midSep _ outArgs.symm (ctxArgs.symm.sub_right (pendSub _))
      (scrArgs.symm.sub_right (lrSub _))) hi]

/-- The test of `out_len`. -/
theorem b0_wp (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    WP isa (.block [.ldrSp .r12 4, .cmp .r12 (.imm 0)]) s
      (fun t => Keep s t ∧ t.z = decide ((stackArg s 1).toNat = 0)) := by
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) rfl
    (argIn (by rw [hs.2.2.1]; simp) (by decide) hs.2.1) fun t₁ u₁ => wp_cmp (op2_imm (by decide)) fun t₂ f₂ z₂ =>
      WP.block_nil ⟨⟨fun r hr => by rw [f₂.gpr, u₁.other _ hr], by rw [f₂.mem, u₁.mem],
        by rw [f₂.rd, u₁.rd], by rw [f₂.wr, u₁.wr], by rw [f₂.sp, u₁.sp]⟩, ?_⟩
  rw [z₂, u₁.gpr, ofNat_toNat32 (s.mem.readW (stackArgAddr s 1) 32), cmp0 (BitVec.isLt _)]; rfl

theorem update_wp (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    WP isa (update d) s (UpdPost d s) := by
  rw [update]
  refine WP.seq (WP.mono (b0_wp d s hs) fun t₂ ⟨ht, hz⟩ => ?_)
  refine WP.ite (decide ((stackArg s 1).toNat = 0)) (by rw [← hz]; rfl) (fun h => ?_) fun h => ?_
  · exact short_ok d s hs (of_decide_eq_true h) t₂ ht
  · exact long_ok d s hs (of_decide_eq_false h) t₂ ht fun t' ht' => call_ok d s hs (of_decide_eq_false h) t' ht'

theorem update_correct (d : Spec.Rc2.Direction) (s : State) (hs : (updateContract d).pre s) :
    ∃ t s', Exec isa (update d) s t s' ∧ abiPreserved s s' ∧ (updateContract d).post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := update_wp d s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

end VG.Proof.Rc2.Arm.Stream
