import VerifiedGarbage.Proof.Rc2.Arm.Stream.InitBody

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` is correct

Untrusted: everything here is checked by Lean. -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd op2_reg wp_ldr wp_ldrSp eval_ne)

/-- The postcondition of `init`: the callee-saved registers and the contract's. -/
abbrev InitPost (s s' : State) : Prop := (∀ r ∈ preserved, s'.gpr r = s.gpr r) ∧ initContract.post s s'

theorem key_pre (s : State) (hs : initContract.pre s) (hv : IValid s) (u : State) (hu : ArgsPost s u) :
    KeyPre u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) := by
  obtain ⟨sp8, _, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, _, _, bKey, _, bCtx, bScr, _, fitK, _, fitC, fitS⟩ := hs
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have eb : (⟨State.addr u.sp - 8, 8⟩ : Region) = ⟨State.addr s.sp - 8, 8⟩ := by rw [hu.sp]
  refine ⟨hu.r0, hu.r1, hu.r2, hu.r3, hu.r12, by rw [hu.sp]; exact sp8,
    ⟨hv.1.1, hv.1.2, hv.2.1.1, hv.2.1.2⟩, keyCtx.sub_right p128, keyScr.sub_right p512,
    (ctxScr.sub_left p128).sub_right p512, ?_, ?_, ?_, fitK, by omega, by omega, ?_, ?_⟩
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bKey
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bCtx.sub_right p128
  · show (Region.mk (State.addr u.sp - 8) 8).Disjoint _; rw [eb]; exact bScr.sub_right p512
  · rw [hu.rd, hu.wr, hrd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩, by simp, 0, (add0 _).symm, by simp⟩
  · rw [hu.wr, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (stackArg s 1), 144⟩, by simp, 0, (add0 _).symm, by simp⟩
      · exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, 0, (add0 _).symm, by simp⟩

theorem tail_ok (s : State) (hs : initContract.pre s) (hv : IValid s) (u : State) (hu : ArgsPost s u)
    (v : State) (hk : KeyPost u (s.gpr .r0) (s.gpr .r1) (s.gpr .r2) (stackArg s 1) (stackArg s 2) v) :
    WP isa (.block (restoreLr ++ ([.mov .r0 (.imm 0)] : List Instr))) v (InitPost s) := by
  obtain ⟨_, spfit, hrd, hwr, keyCtx, keyScr, _, _, ctxScr, ctxArgs, scrArgs, bKey, _, bCtx, bScr, bArgs,
    fitK, _, fitC, fitS⟩ := hs
  have eb : below u = ⟨State.addr s.sp - 8, 8⟩ := by simp only [below, hu.sp]
  have frame₂ := hk.frame
  rw [eb] at frame₂
  have p128 : Region.Sub ⟨State.addr (stackArg s 1), 128⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Region.sub_prefix (by decide)
  have i128 : Region.Sub ⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩ ⟨State.addr (stackArg s 1), 144⟩ :=
    Offset.sub_base _ (by decide)
  have p512 : Region.Sub ⟨State.addr (stackArg s 2), 512⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Region.sub_prefix (by decide)
  have l512 : Region.Sub ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩ ⟨State.addr (stackArg s 2), 576⟩ :=
    Offset.sub_base _ (by decide)
  rw [show restoreLr ++ [.mov .r0 (.imm 0)] = [.ldrSp .r12 8, .ldr .lr .r12 512, .mov .r0 (.imm 0)] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hk.sp, hu.sp]; rfl)
    (by rw [hk.rd, hk.wr, hu.rd, hu.wr]; exact argIn (by rw [hrd]; simp) (by decide) spfit) fun v₁ w₁ => ?_
  have hc2 : (⟨stackArgAddr s 0, 12⟩ : Region).Contains (stackArgAddr s 2) (32 / 8) := by
    rw [stackArgAddr_eq s (i := 2) (by decide) spfit]; exact Offset.contains_base _ (by decide) (by decide)
  have argsS : v.mem.readW (stackArgAddr s 2) 32 = stackArg s 2 := by
    rw [frame₂.readW hc2 (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ctxArgs.symm.sub_right p128
        · exact scrArgs.symm.sub_right p512
        · exact bArgs.symm) (by decide)]
    refine stackArg_frame hu.frame spfit (fun r hr => ?_) (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right i128
    · exact scrArgs.symm.sub_right l512
  refine wp_ldr (a := State.addr (stackArg s 2) + BitVec.ofNat 64 512) (by decide)
    (by rw [w₁.gpr, argsS]; exact addr_add (by omega))
    (by rw [w₁.rd, w₁.wr, hk.rd, hk.wr, hu.rd, hu.wr, hwr]
        exact ⟨⟨State.addr (stackArg s 2), 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun v₂ w₂ => wp_mov_imm (by decide) (WP.block_nil ?_)
  have lr₂ : v₂.gpr .lr = s.gpr .lr := by
    rw [w₂.gpr, w₁.mem, frame₂.readW (r := ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩)
      (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ((ctxScr.sub_left p128).sub_right l512).symm
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (bScr.sub_right l512).symm) (by decide), hu.lr]
  have mem₂ : v₂.mem = v.mem := by rw [w₂.mem, w₁.mem]
  refine ⟨fun r hr => ?_, ?_⟩
  · by_cases hl : r = .lr
    · subst hl; rw [gpr_setReg_of_ne _ _ (by decide), lr₂]
    · obtain ⟨h0, _, _, _, h12⟩ := preserved_ne hr hl
      rw [gpr_setReg_of_ne _ _ h0, w₂.other _ hl, w₁.other _ h12, hk.saved r hr hl, hu.callee r hr hl]
  · have hsched : Spec.Rc2.scheduleAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1)) =
        Spec.Rc2.expandKey (Spec.Rc2.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (s.gpr .r2).toNat := by
      rw [mem_setReg, mem₂, hk.sched, Proof.Rc2.bytesAt_frame hu.frame _ _ (by omega) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact keyCtx.sub_right i128
        · exact keyScr.sub_right l512)]
    have hiv : Spec.Rc2.blockAt (v₂.setReg .r0 0).mem (State.addr (stackArg s 1) + 128) =
        Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3)) := by
      rw [mem_setReg, mem₂, e128, Proof.Rc2.blockAt_frame frame₂ _ (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (ctxScr.sub_left i128).sub_right p512
        · exact (bCtx.sub_right i128).symm), hu.iv]
    exact init_post hv.1 hv.2.1 hv.2.2 (by rw [setWidth_append, gpr_setReg_self]) hsched hiv

theorem init_wp (s : State) (hs : initContract.pre s) : WP isa init s (InitPost s) := by
  rw [init]
  refine WP.seq (WP.mono (checks_ok s hs) fun c hc => ?_)
  by_cases hv : IValid s
  · refine WP.ite false (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun h => absurd h (by simp))
      fun _ => ?_
    rw [initBody]
    exact WP.seq (WP.mono (args_ok s hs hv c hc) fun u hu =>
      WP.seq (WP.mono (key_call (key_pre s hs hv u hu)) fun v hk => tail_ok s hs hv u hu v hk))
  · refine WP.ite true (by show eval .ne c = _; rw [eval_ne, hc.z]; simp [hv]) (fun _ => WP.block_nil ?_)
      (fun h => absurd h (by simp))
    refine ⟨fun r hr => ?_, ?_⟩
    · have h : r ≠ .r0 ∧ r ≠ .r12 := by
        by_cases hl : r = .lr
        · subst hl; decide
        · obtain ⟨h0, _, _, _, h12⟩ := preserved_ne hr hl; exact ⟨h0, h12⟩
      exact hc.keep r h.1 h.2
    · exact init_post_error (by rw [setWidth_append]; exact hc.err hv) hv

theorem init_correct (s : State) (hs : initContract.pre s) :
    ∃ t s', Exec isa init s t s' ∧ abiPreserved s s' ∧ initContract.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := init_wp s hs
  exact ⟨t, s', he, ⟨ha, VG.Arm.Exec.sp he⟩, hp⟩

end VG.Proof.Rc2.Arm.Stream
