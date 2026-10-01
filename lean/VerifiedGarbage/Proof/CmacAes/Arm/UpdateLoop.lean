import VerifiedGarbage.Proof.CmacAes.Arm.Update

/-!
# AES-CMAC on ARMv7: the loop of `vg_cmac_aes_update`

Untrusted: everything here is checked by Lean. One block keeps the loop
invariant (`body_ok`): the counter block is `C ⊕ Mᵢ` and the state is
zeroed (`Cmac.chainMem4`), and the call of `vg_aes_ctr32` leaves
`CIPH_K(C ⊕ Mᵢ)` in the state.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs eval_ne ofNat_beq_zero sub_ofNat)

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-! ## Memory outside the writable regions -/

/-- The regions the function writes, with the stack below it. -/
abbrev Big (s₀ : State) : List Region := [stR s₀, scrR s₀, belowR s₀]

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m (State.addr (W s₀)) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.b_data.symm.sub_left (UPre.data_sub hk)

omit hp in
theorem UPre.big_of {m : Mem} (hf : Frame [stR s₀, ⟨State.addr (S s₀), 2064⟩, belowR s₀] (savedMem s₀) m) :
    Frame (Big s₀) s₀.mem m := by
  have f₀ : Frame (Big s₀) s₀.mem (savedMem s₀) :=
    (savedMem_frame s₀).sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
  exact f₀.trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨belowR s₀, by simp, fun _ h => h⟩)

end

/-! ## One block -/

/-- The counter block's address. -/
abbrev Cb (s₀ : State) : BitVec 32 := S s₀ + BitVec.ofNat 32 2048

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CallPre s₁ (W s₀) (Cb s₀) (St s₀) (S s₀) (R s₀) .r9 .r10
  keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s₁.gpr r = s.gpr r
  sp : s₁.sp = s.sp
  mem : s₁.mem = Proof.Cmac.chainMem4 s.mem (State.addr (S s₀) + BitVec.ofNat 64 2048) (State.addr (St s₀))
    (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem chainIn_eq : chainIn ++ updArgs = xorBlk .r0 .r1 .r6 .r7 .r10 0 0 2048 ++
    (.mov .r0 (.imm 0) :: (zeroBlk .r0 .r6 0 ++
      ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5), .dp .add .r2 .r10 (.imm (BitVec.ofNat 32 2048)),
       .mov .r3 (.reg .r6), .mov .r9 (.imm 1)] : List Instr))) := rfl

theorem bodyA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hW : s.wr = [stR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hsc := hp.scr_fit
  have hst := hp.st_fit
  have hdf := hp.data_fit
  have qN := hp.dataN hk
  rw [chainIn_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r6]; omega) (by rw [h.r7, qN]; omega)
    (by rw [h.r10]; omega) ?_ ?_ ?_ fun s₁ g₁ => ?_
  · rw [h.r6, add0, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  · rw [h.r7, add0, hp.dataA hk, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
  · rw [h.r10, hW]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
  have e₁ : ∀ r, r ≠ .r0 → r ≠ .r1 → s₁.gpr r = s.gpr r := g₁.gpr
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have r6₂ : s₂.gpr .r6 = St s₀ := by rw [u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r6]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r6₂]; omega) ?_ fun s₃ G₃ m₃ rd₃ wr₃ sp₃ => ?_
  · rw [r6₂, add0, u₂.wr, g₁.wr, hW]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_add (op2_imm (by decide)) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ =>
    wp_mov (op2_imm (by decide)) fun s₈ u₈ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r0 → r ≠ .r1 → r ≠ .r2 → r ≠ .r3 → r ≠ .r9 → s₈.gpr r = s.gpr r :=
    fun r h0 h1 h2 h3 h9 => by
      rw [u₈.other _ h9, u₇.other _ h3, u₆.other _ h2, u₅.other _ h1, u₄.other _ h0, G₃, u₂.other _ h0,
        e₁ _ h0 h1]
  have sp₈ : s₈.sp = s₀.sp := by
    rw [u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, g₁.sp, h.sp]
  have rd₈ : s₈.rd = s.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, g₁.rd]
  have wr₈ : s₈.wr = s.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, g₁.wr]
  have mem₈ : s₈.mem = Proof.Cmac.chainMem4 s.mem (State.addr (S s₀) + BitVec.ofNat 64 2048)
      (State.addr (St s₀)) (State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k)) := by
    rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, m₃, r6₂, u₂.mem, g₁.mem, h.r6, h.r7, h.r10, add0, add0,
      hp.dataA hk]
    rfl
  have hb : below s₈ = belowR s₀ := by rw [below, sp₈]; rfl
  have cA : State.addr (Cb s₀) = State.addr (S s₀) + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have cSt : (⟨State.addr (Cb s₀), 16⟩ : Region).Disjoint (stR s₀) := by
    rw [cA]; exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, u₈.gpr, ?_, by decide, hp.rounds, by rw [sp₈]; exact hp.sp8, ?_, hp.sch_st, ?_, cSt,
    ?_, ?_, by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_st, ?_, hp.sch_fit, ?_, hp.st_fit, ?_, ?_, ?_,
    ?_⟩, keep, by rw [sp₈, h.sp], mem₈, rd₈, wr₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r4]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r5]
    simp [R]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      G₃, u₂.other _ (by decide), e₁ _ (by decide) (by decide), h.r10]
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      G₃, r6₂]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [cA]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
  · exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hb, cA]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hp.scrN (by decide)]; omega
  · omega
  · rw [rd₈, wr₈, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hW, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₈]; exact Proof.Cmac.chainMem4_state _ _ _ _

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa body s fun s' => LInv s₀ (k + 1) s' ∧ s'.z = decide (N s₀ - (k + 1) = 0) := by
  have hdf := hp.data_fit
  have hN := (stackArg s₀ 0).isLt
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (ctr_call a.pre) fun s₂ h₂ => ?_)
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_subs (op2_imm (by decide)) fun s₄ u₄ z₄ => WP.block_nil ?_
  have g (r : Reg) (hr : r ∈ preserved) (hlr : r ≠ .lr) (h7 : r ≠ .r7) (h8 : r ≠ .r8) (h9 : r ≠ .r9) :
      s₄.gpr r = s.gpr r := by
    have : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [u₄.other _ h8, u₃.other _ h7, h₂.saved r hr hlr, a.keep r this.1 this.2.1 this.2.2.1 this.2.2.2 h9]
  have r7₂ : s₂.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [h₂.saved .r7 (by simp [preserved]) (by decide), a.keep _ (by decide) (by decide) (by decide) (by decide)
      (by decide), h.r7]
  have r8₃ : s₃.gpr .r8 = BitVec.ofNat 32 (N s₀ - k) := by
    rw [u₃.other _ (by decide), h₂.saved .r8 (by simp [preserved]) (by decide),
      a.keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r8]
  have dec : BitVec.ofNat 32 (N s₀ - k) - 1 = BitVec.ofNat 32 (N s₀ - (k + 1)) := by
    rw [show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  -- Memory.
  have bigS := UPre.big_of h.frame
  have cA : State.addr (Cb s₀) = State.addr (S s₀) + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have f₁ : Frame [⟨State.addr (S s₀) + BitVec.ofNat 64 2048, 16⟩, stR s₀] s.mem s₁.mem := by
    rw [a.mem]; exact Proof.Cmac.chainMem4_frame _ _ _ _
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := (UPre.big_of h.frame).trans (f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨scrR s₀, by simp, UPre.scr_sub (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  have cst : (⟨State.addr (S s₀) + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨State.addr (S s₀) + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint
      ⟨State.addr (Dp s₀) + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, cA, a.mem, Proof.Cmac.chainMem4_counter _ cst cq, h.state,
    UPre.block_bytes hp bigS hk] at out
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [g .r4 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r4]
  · rw [g .r5 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r5]
  · rw [g .r6 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r6]
  · rw [u₄.other _ (by decide), u₃.gpr, r7₂, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [u₄.gpr, r8₃, dec]
  · rw [g .r10 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r10]
  · rw [g .r11 (by simp [preserved]) (by decide) (by decide) (by decide) (by decide), h.r11]
  · rw [u₄.sp, u₃.sp, h₂.sp, a.sp, h.sp]
  · rw [u₄.rd, u₃.rd, h₂.rd, a.rd, h.rd]
  · rw [u₄.wr, u₃.wr, h₂.wr, a.wr, h.wr]
  · have hb : below s₁ = belowR s₀ := by rw [below, a.sp, h.sp]; rfl
    rw [u₄.mem, u₃.mem]
    refine h.frame.trans ((f₁.sub fun r hr => ?_).trans (h₂.frame.sub fun r hr => ?_))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, by rw [cA]; exact Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨State.addr (S s₀), 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨belowR s₀, by simp, by rw [hb]; exact fun _ h => h⟩
  · rw [u₄.mem, u₃.mem, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]
  · rw [z₄, r8₃, dec]; exact ofNat_beq_zero (by omega)

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.loop body .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s' = _; rw [eval_ne, hz]
  by_cases hz' : N s₀ - (k + 1) = 0
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [show N s₀ = k + 1 by omega]
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

end VG.Proof.CmacAes.Arm
