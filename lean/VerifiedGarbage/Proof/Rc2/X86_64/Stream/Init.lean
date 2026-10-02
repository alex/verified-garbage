import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Checks
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Lit

/-! # Streaming RC2-CBC on x86-64: `vg_rc2_cbc_init` -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

theorem initArgs_ok (s : State) (riv : InRegions (s.rd ++ s.wr) (s.gpr .rcx + BitVec.ofNat 64 0) 8)
    (wctx : InRegions s.wr (s.gpr .r9 + BitVec.ofNat 64 128) 8)
    (rarg : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 8) 8) :
    ∃ s', runBlock isa initArgs s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .r9 + BitVec.ofNat 64 128) (s.mem.readW (s.gpr .rcx + BitVec.ofNat 64 0) 64) ∧
      s'.gpr .rcx = s.gpr .r9 ∧ s'.gpr .r8 = s'.mem.readW (s.gpr .rsp + BitVec.ofNat 64 8) 64 ∧
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [initArgs, rr, memOp, runBlock_cons, runStep_some,
      exec, readSrc, State.load64, State.store64, State.ea, offset_nat, Option.map_some,
      gpr_setReg_self, gpr_setReg_of_ne, rd_setReg, wr_setReg, mem_setReg, riv, wctx, ite_true]
    simp only [rarg, ite_true, Option.map_some]
    rfl, ?_⟩
  refine ⟨rfl, ?_, ?_, fun r h₁ h₂ h₃ => ?_, rfl, rfl⟩
  · simp (config := {decide := true}) only [gpr_setReg_self, gpr_setReg_of_ne]
  · simp only [gpr_setReg_self, mem_setReg]
  · simp only [gpr_setReg_of_ne _ _ h₁, gpr_setReg_of_ne _ _ h₂, gpr_setReg_of_ne _ _ h₃]

/-- The state before the call of key expansion, from the entry state `σ`. -/
structure KeyPre (σ t : State) : Prop where
  rdi : t.gpr .rdi = σ.gpr .rdi
  rsi : t.gpr .rsi = σ.gpr .rsi
  rdx : t.gpr .rdx = σ.gpr .rdx
  rcx : t.gpr .rcx = σ.gpr .r9
  r8 : t.gpr .r8 = stackArg σ 0
  rsp : t.gpr .rsp = σ.gpr .rsp
  callee : ∀ r ∈ calleeSaved, t.gpr r = σ.gpr r
  rd : t.rd = σ.rd
  wr : t.wr = σ.wr
  mem : t.mem = σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 128) (σ.mem.readW (σ.gpr .rcx) 64)

/-- Valid lengths. -/
def Valid (σ : State) : Prop :=
  (1 ≤ (σ.gpr .rsi).toNat ∧ (σ.gpr .rsi).toNat ≤ 128) ∧ (1 ≤ (σ.gpr .rdx).toNat ∧ (σ.gpr .rdx).toNat ≤ 1024) ∧
    (σ.gpr .r8).toNat = 8

theorem valid_of_code {σ : State} (h : code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat = 0) :
    Valid σ := by
  unfold code at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · refine ⟨?_, ?_, ?_⟩ <;> simp_all

theorem initArgs_pre (σ : State) (hs : initContract.pre σ) (hv : Valid σ) (t : State) (ht : Keep [.rax, .r10] σ t) :
    WP isa (.block initArgs) t (KeyPre σ) := by
  obtain ⟨_, _, hrd, hwr, _, _, _, _, _, ctxArgs, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hs
  have rdwr {a : Addr} {n : Nat} (h : InRegions σ.rd a n) : InRegions (σ.rd ++ σ.wr) a n := by
    obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_left _ hr, hc⟩
  have argsAddr : stackArgAddr σ 0 = σ.gpr .rsp + BitVec.ofNat 64 8 := rfl
  obtain ⟨t', run, mem', rcx', r8', g', rd', wr'⟩ := initArgs_ok t
    (by rw [ht.rd, ht.wr, ht.reg _ (by decide)]
        exact rdwr (by rw [hrd]; exact ⟨⟨σ.gpr .rcx, (σ.gpr .r8).toNat⟩, by simp,
          Offset.contains_base _ (by have := hv.2.2; omega) (by decide)⟩))
    (by rw [ht.wr, ht.reg _ (by decide), hwr]
        exact ⟨⟨σ.gpr .r9, 144⟩, by simp, Offset.contains_base _ (by decide) (by decide)⟩)
    (by rw [ht.rd, ht.wr, ht.reg _ (by decide), ← argsAddr]
        exact rdwr (by rw [hrd]; exact ⟨⟨stackArgAddr σ 0, 8⟩, by simp, Region.contains_self _ _⟩))
  refine WP.of_runBlock ⟨t', run, ?_⟩
  have m : t'.mem = σ.mem.writeW (σ.gpr .r9 + BitVec.ofNat 64 128) (σ.mem.readW (σ.gpr .rcx) 64) := by
    rw [mem', ht.mem, ht.reg _ (by decide), ht.reg _ (by decide),
      show σ.gpr .rcx + BitVec.ofNat 64 0 = σ.gpr .rcx from BitVec.add_zero _]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, by rw [rd', ht.rd], by rw [wr', ht.wr], m⟩
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · rw [rcx', ht.reg _ (by decide)]
  · rw [r8', ht.reg _ (by decide), m, ← argsAddr]
    exact (frame_store64 _ _ _).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ctxArgs.symm.sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rw [g' _ (by decide) (by decide) (by decide), ht.reg _ (by decide)]
  · have h : r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .r8 ∧ r ∉ [Reg.rax, .r10] := by revert hr; revert r; decide
    rw [g' _ h.1 h.2.1 h.2.2.1, ht.reg _ h.2.2.2]

def keyRd (σ : State) : List Region := [⟨σ.gpr .rdi, (σ.gpr .rsi).toNat⟩]
def keyWr (σ : State) : List Region := [⟨σ.gpr .r9, 128⟩, ⟨stackArg σ 0, 512⟩]

/-- Key expansion's precondition at the call, and its regions within ours. -/
theorem key_pre (σ : State) (hs : initContract.pre σ) (hv : Valid σ) (t : State) (ht : KeyPre σ t) :
    keyContract.pre (t.callEntry.withRegions (keyRd σ) (keyWr σ)) ∧
      Covers (keyRd σ ++ keyWr σ) (t.rd ++ t.wr) ∧ Covers (keyWr σ) t.wr := by
  obtain ⟨_, _, hrd, hwr, keyCtx, keyBuf, _, _, ctxBuf, _, _, _, _, _, _, _, _, _, stCtx, stBuf, _, _, _, _, _⟩ := hs
  have keySub : Region.Sub ⟨σ.gpr .r9, 128⟩ ⟨σ.gpr .r9, 144⟩ := Region.sub_prefix (by decide)
  have bufSub : Region.Sub ⟨stackArg σ 0, 512⟩ ⟨stackArg σ 0, 576⟩ := Region.sub_prefix (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp only [keyContract, keyRd, keyWr, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
      State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      ht.rdi, ht.rsi, ht.rdx, ht.rcx, ht.r8, ht.rsp]
    exact ⟨trivial, trivial, keyCtx.sub_right keySub, keyBuf.sub_right bufSub, (ctxBuf.sub_left keySub).sub_right bufSub,
      stCtx.sub_right keySub, stBuf.sub_right bufSub, hv.1.1, hv.1.2, hv.2.1.1, hv.2.1.2⟩
  · rw [ht.rd, ht.wr, hrd, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [keyRd, keyWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨⟨σ.gpr .rdi, (σ.gpr .rsi).toNat⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨σ.gpr .r9, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨stackArg σ 0, 576⟩, by simp, 0, by simp, by simp⟩
  · rw [ht.wr, hwr]
    apply Covers.of_sub
    intro r hr
    simp only [keyWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨σ.gpr .r9, 144⟩, by simp, 0, by simp, by simp⟩
    · exact ⟨⟨stackArg σ 0, 576⟩, by simp, 0, by simp, by simp⟩

theorem expandKey_noSp : NoSp expandKey := by
  have h : ((instrs expandKey).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi
  simpa using List.all_eq_true.mp h i hi

theorem expandKey_depth : expandKey.depth = 0 := rfl

/-- The postcondition of `init`, spelled out. -/
def InitPost (σ s' : State) : Prop :=
  ((∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) ∧ s'.mem.readW (σ.gpr .rsp) 64 = σ.mem.readW (σ.gpr .rsp) 64) ∧
  ∀ direction, match Spec.Rc2.initWithEffectiveBits (Spec.Rc2.bytesAt σ.mem (σ.gpr .rdi) (σ.gpr .rsi).toNat)
      (Spec.Rc2.bytesAt σ.mem (σ.gpr .rcx) (σ.gpr .r8).toNat) direction (σ.gpr .rdx).toNat with
    | .ok c => (s'.gpr .rax).setWidth 32 = 0 ∧ Spec.Rc2.contextAt s'.mem (σ.gpr .r9) direction 0 = c
    | .error e => ((s'.gpr .rax).setWidth 32).toNat = e.code

theorem keyCall_ok (σ : State) (hs : initContract.pre σ) (hv : Valid σ) (t : State) (ht : KeyPre σ t) :
    WP isa (.seq keyCall (.block [.mov32 .rax (.imm 0)])) t (InitPost σ) := by
  obtain ⟨hpre, hc, hw⟩ := key_pre σ hs hv t ht
  simp only [keyRd, keyWr] at hpre hc hw
  obtain ⟨_, _, hrd, hwr, keyCtx, keyBuf, _, _, ctxBuf, _, _, retKey, _, retCtx, retBuf, _, stKey, _, stCtx, stBuf, _,
    _, _, _, _⟩ := hs
  have pendSub : Region.Sub ⟨σ.gpr .r9 + BitVec.ofNat 64 128, 8⟩ ⟨σ.gpr .r9, 144⟩ := Offset.sub_base _ (by decide)
  have bufSub : Region.Sub ⟨stackArg σ 0, 512⟩ ⟨stackArg σ 0, 576⟩ := Region.sub_prefix (by decide)
  have keySub : Region.Sub ⟨σ.gpr .r9, 128⟩ ⟨σ.gpr .r9, 144⟩ := Region.sub_prefix (by decide)
  refine WP.seq (WP.call (k := keyContract) key_correct expandKey_noSp (by rw [expandKey_depth]; decide)
    hpre hc hw ?_)
  intro s' _ _ callee' frame' _ ⟨s₂, mem₂, _, post₂⟩
  rw [expandKey_depth, ht.rsp] at frame'
  have stackFrame : Frame [below (σ.gpr .rsp) 8] t.mem t.callEntry.mem := by
    rw [State.callEntry_mem, ht.rsp]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (below_call _ (by decide) (by decide))
  simp only [keyContract, State.withRegions_gpr, State.withRegions_mem,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    ht.rdi, ht.rsi, ht.rdx, ht.rcx, mem₂] at post₂
  rw [Proof.Rc2.bytesAt_frame stackFrame _ _ (by omega) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact stKey.symm),
    ht.mem, Proof.Rc2.bytesAt_frame (frame_store64 _ _ _) _ _ (by omega) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact keyCtx.sub_right pendSub)] at post₂
  obtain ⟨s'', run, rax'', keep''⟩ := zero_ok s'
  refine WP.of_runBlock ⟨s'', run, ⟨fun r hr => ?_, ?_⟩, fun direction => ?_⟩
  · rw [keep''.reg r (by revert hr; revert r; decide), callee' r hr, ht.callee r hr]
  · have callSep (R : Region) (hctx : R.Disjoint ⟨σ.gpr .r9, 144⟩) (hbuf : R.Disjoint ⟨stackArg σ 0, 576⟩)
        (hst : R.Disjoint (below (σ.gpr .rsp) 8)) :
        ∀ r ∈ [(⟨σ.gpr .r9, 128⟩ : Region), ⟨stackArg σ 0, 512⟩] ++ [below (σ.gpr .rsp) 8], R.Disjoint r := by
      intro r hr
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hctx.sub_right keySub
      · exact hbuf.sub_right bufSub
      · exact hst
    rw [keep''.mem, frame'.readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _)
        (callSep _ retCtx retBuf (Offset.base_disjoint_below _ (by decide))) (by decide), ht.mem,
      (frame_store64 _ _ _).readW (r := ⟨σ.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact retCtx.sub_right pendSub) (by decide)]
  · refine init_post (m' := s''.mem) (r := (s''.gpr .rax).setWidth 32) hv.1 hv.2.1 hv.2.2 (by rw [rax'']; rfl) (by rw [keep''.mem]; exact post₂) (iv := σ.gpr .rcx) ?_ direction
    rw [keep''.mem, show σ.gpr .r9 + 128 = σ.gpr .r9 + BitVec.ofNat 64 128 from rfl,
      blockAt_frame frame' _ (fun r hr => by
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact Offset.disjoint_base _ (by decide) (by decide)
        · exact (ctxBuf.sub_left pendSub).sub_right bufSub
        · exact (stCtx.sub_right pendSub).symm),
      ht.mem, blockAt_copy]

theorem code_ne {a b c : Nat} (h : code a b c ≠ 0) :
    code a b c = if ¬(1 ≤ a ∧ a ≤ 128) then 1 else if ¬(1 ≤ b ∧ b ≤ 1024) then 2 else 3 := by
  unfold code at h ⊢
  by_cases h₃ : c ≠ 8
  · simp [h₃]
  · simp only [h₃, ↓reduceIte] at h ⊢
    split at h <;> simp_all

theorem init_body_correct (σ : State) (hs : initContract.pre σ) : WP isa init σ (InitPost σ) := by
  refine WP.seq (WP.mono (checks_ok σ) fun t ⟨keep, zf, rax⟩ => ?_)
  refine WP.ite _ (by simp only [eval, zf]; rfl) (fun h => WP.block_nil ?_) (fun h => ?_)
  · have hc : code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat ≠ 0 := by simpa using h
    have hr : ((t.gpr .rax).setWidth 32).toNat = code (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat := by
      have := code_le (σ.gpr .rsi).toNat (σ.gpr .rdx).toNat (σ.gpr .r8).toNat
      rw [rax, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨fun r hr' => keep.reg r (by revert hr'; revert r; decide), by rw [keep.mem]⟩, ?_⟩
    refine init_post_error (hr.trans (code_ne hc)) (fun hv => hc ?_)
    simp only [code, hv.1, hv.2.1, hv.2.2, not_true_eq_false, and_self, ↓reduceIte, ne_eq]
  · have hv := valid_of_code (σ := σ) (by simpa using h)
    exact WP.seq (WP.mono (initArgs_pre σ hs hv t keep) fun t' ht' => keyCall_ok σ hs hv t' ht')

theorem init_correct (σ : State) (hs : initContract.pre σ) :
    ∃ t s', Exec isa init σ t s' ∧ abiPreserved σ s' ∧ initContract.post σ s' := by
  obtain ⟨t, s', he, ha, hp⟩ := init_body_correct σ hs
  exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he ha, hp⟩

end VG.Proof.Rc2.X86_64.Stream
