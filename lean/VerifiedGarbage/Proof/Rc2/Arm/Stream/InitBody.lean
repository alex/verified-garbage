import VerifiedGarbage.Proof.Rc2.Arm.Stream.Init

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init` once the lengths are valid

Untrusted: everything here is checked by Lean. -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_ldr wp_str wp_ldrSp eval_ne)

/-- The state before the call of `vg_rc2_expand_key`, from the entry state `s`. -/
structure ArgsPost (s u : State) : Prop where
  r0 : u.gpr .r0 = s.gpr .r0
  r1 : u.gpr .r1 = s.gpr .r1
  r2 : u.gpr .r2 = s.gpr .r2
  r3 : u.gpr .r3 = stackArg s 1
  r12 : u.gpr .r12 = stackArg s 2
  callee : ∀ r ∈ preserved, r ≠ .lr → u.gpr r = s.gpr r
  sp : u.sp = s.sp
  rd : u.rd = s.rd
  wr : u.wr = s.wr
  frame : Frame [⟨State.addr (stackArg s 1) + BitVec.ofNat 64 128, 8⟩,
    ⟨State.addr (stackArg s 2) + BitVec.ofNat 64 512, 4⟩] s.mem u.mem
  lr : u.mem.readW (State.addr (stackArg s 2) + BitVec.ofNat 64 512) 32 = s.gpr .lr
  iv : Spec.Rc2.blockAt u.mem (State.addr (stackArg s 1) + BitVec.ofNat 64 128) =
    Spec.Rc2.blockAt s.mem (State.addr (s.gpr .r3))

theorem args_ok (s : State) (hs : initContract.pre s) (hv : IValid s) (c : State) (hc : CheckPost s c) :
    WP isa (.block initArgs) c (ArgsPost s) := by
  obtain ⟨_, spfit, hrd, hwr, _, _, ivCtx, ivScr, ctxScr, ctxArgs, scrArgs, _, _, _, _, _, _, fitIV,
    fitC, fitS⟩ := hs
  have hL : (stackArg s 0).toNat = 8 := hv.2.2
  rw [hL] at ivCtx ivScr fitIV hrd
  have g (r : Reg) (h : r ≠ .r12) : c.gpr r = s.gpr r := by
    by_cases h0 : r = .r0
    · subst h0; exact hc.ok hv
    · exact hc.keep r h0 h
  have argR (i : Nat) (hi : i < 3) : InRegions (s.rd ++ s.wr) (stackArgAddr s i) 4 :=
    argIn (by rw [hrd]; simp) hi spfit
  generalize hIV : s.gpr .r3 = IV at *
  generalize hCt : stackArg s 1 = Ct at *
  generalize hS : stackArg s 2 = S at *
  generalize hLR : s.gpr .lr = LR at *
  have lrSub : Region.Sub ⟨State.addr S + BitVec.ofNat 64 512, 4⟩ ⟨State.addr S, 576⟩ := Offset.sub_base _ (by decide)
  have ivSub' : Region.Sub ⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ ⟨State.addr Ct, 144⟩ :=
    Offset.sub_base _ (by decide)
  have argsSep : ∀ r ∈ [(⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩ : Region),
      ⟨State.addr S + BitVec.ofNat 64 512, 4⟩], (Region.mk (stackArgAddr s 0) 12).Disjoint r := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ctxArgs.symm.sub_right ivSub'
    · exact scrArgs.symm.sub_right lrSub
  rw [show initArgs = [.ldrSp .r12 8, .str .lr .r12 512, .ldr .lr .r3 0, .ldr .r3 .r3 4, .ldrSp .r12 4,
    .str .lr .r12 128, .str .r3 .r12 132, .mov .r3 (.reg .r12), .ldrSp .r12 8] from rfl]
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide) (by rw [hc.sp]; rfl)
    (by rw [hc.rd, hc.wr]; exact argR 2 (by decide)) fun u₁ v₁ => ?_
  have r12₁ : u₁.gpr .r12 = S := by rw [v₁.gpr, hc.mem]; exact hS
  refine wp_str (a := State.addr S + BitVec.ofNat 64 512) (by decide) (by rw [r12₁]; exact addr_add (by omega))
    (by rw [v₁.wr, hc.wr, hwr]; exact ⟨⟨State.addr S, 576⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₂ v₂ => ?_
  have m₂ : u₂.mem = s.mem.writeW (State.addr S + BitVec.ofNat 64 512) LR := by
    rw [v₂.mem, v₁.mem, hc.mem, v₁.other _ (by decide), g _ (by decide), hLR]
  have f₂ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₂.mem := by
    rw [m₂]; exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
  have r3₂ : u₂.gpr .r3 = IV := by rw [v₂.gpr, v₁.other _ (by decide), g _ (by decide), hIV]
  have ivR : InRegions (u₂.rd ++ u₂.wr) (State.addr IV) 8 := by
    rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr, hrd]; exact ⟨_, by simp, Region.contains_self _ _⟩
  have ivRead (k : Nat) (hk : k ≤ 4) : u₂.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 =
      s.mem.readW (State.addr IV + BitVec.ofNat 64 k) 32 := by
    rw [m₂]
    refine Mem.readW_writeW_sep (ivScr.sep (Offset.contains_base _ (by omega) (by omega)) ?_) (by decide)
    exact Offset.contains_base _ (by decide) (by decide)
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 0) (by decide)
    (by rw [r3₂]; exact addr_add (by omega))
    (by obtain ⟨r, hr, hc'⟩ := ivR; exact ⟨r, hr, by rw [add0]; unfold Region.Contains at hc' ⊢; omega⟩)
    fun u₃ v₃ => ?_
  refine wp_ldr (a := State.addr IV + BitVec.ofNat 64 4) (by decide)
    (by rw [v₃.other _ (by decide), r3₂]; exact addr_add (by omega))
    (by rw [v₃.rd, v₃.wr]; exact (Cbc.halves ivR).2) fun u₄ v₄ => ?_
  refine wp_ldrSp (a := stackArgAddr s 1) (by decide) (by rw [v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, hc.rd, hc.wr]; exact argR 1 (by decide))
    fun u₅ v₅ => ?_
  have r12₅ : u₅.gpr .r12 = Ct := by
    rw [v₅.gpr, v₄.mem, v₃.mem, stackArg_frame f₂ spfit argsSep (by decide)]; exact hCt
  have wr₅ : u₅.wr = s.wr := by rw [v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, hc.wr]
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128) (by decide) (by rw [r12₅]; exact addr_add (by omega))
    (by rw [wr₅, hwr]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩) fun u₆ v₆ => ?_
  refine wp_str (a := State.addr Ct + BitVec.ofNat 64 128 + BitVec.ofNat 64 4) (by decide)
    (by rw [v₆.gpr, r12₅, Offset.add_add]; exact addr_add (by omega))
    (by rw [v₆.wr, wr₅, hwr, Offset.add_add]; exact ⟨⟨State.addr Ct, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    fun u₇ v₇ => wp_mov (op2_reg _ _) fun u₈ v₈ => ?_
  refine wp_ldrSp (a := stackArgAddr s 2) (by decide)
    (by rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]; rfl)
    (by rw [v₈.rd, v₈.wr, v₇.rd, v₇.wr, v₆.rd, v₆.wr, v₅.rd, wr₅, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
        exact argR 2 (by decide)) fun u₉ v₉ => WP.block_nil ?_
  -- The memory.
  have w0 : u₅.gpr .lr = s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32 := by
    rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.gpr, ivRead 0 (by decide)]
  have w1 : u₆.gpr .r3 = s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 := by
    rw [v₆.gpr, v₅.other _ (by decide), v₄.gpr, v₃.mem, ivRead 4 (by decide)]
  have m₇ : u₇.mem = u₂.mem.writeW (State.addr Ct + BitVec.ofNat 64 128)
      (s.mem.readW (State.addr IV + BitVec.ofNat 64 4) 32 ++ s.mem.readW (State.addr IV + BitVec.ofNat 64 0) 32) := by
    rw [v₇.mem, w1, v₆.mem, w0, v₅.mem, v₄.mem, v₃.mem, VG.Proof.Rc2.Word32.write64_pair]
  have mem₉ : u₉.mem = u₇.mem := by rw [v₉.mem, v₈.mem]
  have f₇ : Frame [⟨State.addr Ct + BitVec.ofNat 64 128, 8⟩, ⟨State.addr S + BitVec.ofNat 64 512, 4⟩]
      s.mem u₇.mem := by
    rw [m₇]; exact f₂.writeW (by simp) _ (Region.contains_self _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r hr hl => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.other _ (by decide), v₇.gpr, v₆.gpr, v₅.other _ (by decide),
      v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g _ (by decide)]
  · rw [v₉.other _ (by decide), v₈.gpr, v₇.gpr, v₆.gpr, r12₅, hCt]
  · rw [v₉.gpr, v₈.mem, stackArg_frame f₇ spfit argsSep (by decide)]
  · obtain ⟨h0, h1, h2, h3, h12⟩ := preserved_ne hr hl
    rw [v₉.other _ h12, v₈.other _ h3, v₇.gpr, v₆.gpr, v₅.other _ h12, v₄.other _ h3, v₃.other _ hl, v₂.gpr,
      v₁.other _ h12, g _ h12]
  · rw [v₉.sp, v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, hc.sp]
  · rw [v₉.rd, v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, hc.rd]
  · rw [v₉.wr, v₈.wr, v₇.wr, v₆.wr, wr₅]
  · rw [hCt, hS, mem₉]; exact f₇
  · rw [hS, hLR, mem₉, m₇, Mem.readW_writeW_sep (((ctxScr.sub_left ivSub').sub_right lrSub).symm.sep (Region.contains_self _ _)
      (Region.contains_self _ _)) (by decide), m₂, Mem.readW_writeW_self32]
  · rw [hCt, hIV, mem₉, m₇, Proof.Rc2.blockAt_store64, add0, ← VG.Proof.Rc2.Word32.read64_pair,
      ← Proof.Rc2.blockAt_read64]

end VG.Proof.Rc2.Arm.Stream
