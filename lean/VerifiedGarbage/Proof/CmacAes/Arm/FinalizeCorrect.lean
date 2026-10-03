import VerifiedGarbage.Proof.CmacAes.Arm.Finalize

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize` is correct

Before the call, the counter block holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is zeroed;
the call leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC (`Cmac.macFull_split`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd op2_imm op2_reg wp_mov wp_add wp_ldr eval_eq)

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ s : State) : Prop where
  pre : CallPre s (W s₀) (S s₀ + BitVec.ofNat 32 2048) (St s₀) (S s₀) (R s₀) .r4 .r5
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 =
    Spec.Cmac.xor (mn s₀) (Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16)
  frame : Frame [⟨Ca s₀, 16⟩, stR s₀] (fsMem s₀) s.mem
  r5 : s.gpr .r5 = S s₀
  keep : ∀ r ∈ preserved, r ≠ .r4 → r ≠ .r5 → r ≠ .lr → s.gpr r = s₀.gpr r
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_eq : finArgs = xorBlk .r12 .lr .r5 .r2 .r5 2048 0 2048 ++
    (.mov .r12 (.imm 0) :: (zeroBlk .r12 .r2 0 ++
      ([.mov .r3 (.reg .r2), .dp .add .r2 .r5 (.imm (BitVec.ofNat 32 2048)), .mov .r4 (.imm 1)] :
        List Instr))) := rfl

theorem preserved_ne {r : Reg} (hr : r ∈ preserved) : r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 ∧ r ≠ .r12 := by
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem finArgs_wp {s₀ : State} (hp : FPre s₀) {s : State} (h : BPost s₀ s) :
    WP isa (.block finArgs) s (FMid s₀) := by
  have sf := hp.scr_fit
  have tf := hp.st_fit
  have hR := hp.rounds
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have r2 : s.gpr .r2 = St s₀ := h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega)
  have cSt : (⟨Ca s₀, 16⟩ : Region).Disjoint (stR s₀) := hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  have wSt : Covers [stR s₀] s₀.wr := by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  rw [finArgs_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [h.r5]; omega) (by rw [r2]; omega) (by rw [h.r5]; omega)
    (by
      rw [h.r5, hrw]
      exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
        fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by
      rw [r2, add0, hrw]
      exact fun a n hi => wSt a n hi |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [h.r5, h.wr]; exact hp.cS (by decide)) fun s₁ g₁ => ?_
  refine wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have r2₂ : s₂.gpr .r2 = St s₀ := by rw [u₂.other _ (by decide), g₁.gpr _ (by decide) (by decide), r2]
  refine Proof.CmacAes.Arm.zeroBlk_ok u₂.gpr (by decide) (by rw [r2₂]; omega)
    (by rw [r2₂, add0, u₂.wr, g₁.wr, h.wr]; exact wSt) fun s₃ G₃ m₃ rd₃ wr₃ sp₃ => ?_
  refine wp_mov (op2_reg _ _) fun s₄ u₄ => wp_add (op2_imm (by decide)) fun s₅ u₅ =>
    wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .r2 → r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₆.gpr r = s.gpr r :=
    fun r h2 h3 h4 h12 hlr => by
      rw [u₆.other _ h4, u₅.other _ h2, u₄.other _ h3, G₃, u₂.other _ h12, g₁.gpr _ h12 hlr]
  have r5₆ : s₆.gpr .r5 = S s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r5]
  have sp₆ : s₆.sp = s₀.sp := by rw [u₆.sp, u₅.sp, u₄.sp, sp₃, u₂.sp, g₁.sp, h.sp]
  have rd₆ : s₆.rd = s₀.rd := by rw [u₆.rd, u₅.rd, u₄.rd, rd₃, u₂.rd, g₁.rd, h.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [u₆.wr, u₅.wr, u₄.wr, wr₃, u₂.wr, g₁.wr, h.wr]
  have mem₆ : s₆.mem = Proof.Cmac.zero4 (Proof.Cmac.xor4Mem s.mem (Ca s₀) (Ca s₀) (State.addr (St s₀)))
      (State.addr (St s₀)) := by
    rw [u₆.mem, u₅.mem, u₄.mem, m₃, r2₂, add0, u₂.mem, g₁.mem, h.r5, r2, add0]
  have hb : below s₆ = belowR s₀ := by rw [below, sp₆]; rfl
  have stS : Spec.Aes.bytesAt s.mem (State.addr (St s₀)) 16 = Spec.Aes.bytesAt s₀.mem (State.addr (St s₀)) 16 :=
    Proof.Cmac.bytesAt_frame16 ((fsMem_frame s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr
  refine ⟨?_, ?_, ?_, r5₆, fun r hr h4 h5 hlr => ?_, sp₆, rd₆, wr₆⟩
  · exact
    { r0 := by rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]
      r1 := by
        rw [keep _ (by decide) (by decide) (by decide) (by decide) (by decide),
          h.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [R]
      r2 := by rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), G₃, u₂.other _ (by decide),
          g₁.gpr _ (by decide) (by decide), h.r5]
      r3 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, G₃, r2₂]
      hra := u₆.gpr
      hrb := r5₆
      regs := by decide
      rounds := hR
      hsp := by rw [sp₆]; exact hp.sp8
      wc := by rw [cA]; exact (hp.ca_key (d := 0) (n := 240) (by decide)).symm |> fun d => by simpa using d
      wd := hp.key_st.sub_left (Region.sub_prefix (by decide))
      ws := (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
      cd := by rw [cA]; exact cSt
      cs := by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
      ds := hp.st_scr.sub_right (Region.sub_prefix (by decide))
      bw := by rw [hb]; exact hp.b_key.sub_right (Region.sub_prefix (by decide))
      bc := by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide))
      bd := by rw [hb]; exact hp.b_st
      bs := by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
      hW := by have := hp.key_fit; omega
      hC := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega
      hD := tf
      hS := by omega
      reads := by
        rw [rd₆, wr₆, hp.rd]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact ⟨keyR s₀, by simp, 0, by simp, by simp⟩
      writes := by
        rw [wr₆, hp.wr, cA]
        refine Covers.of_sub fun r hr => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
        · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
        · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
      zero := by rw [mem₆]; exact Proof.Cmac.zero4_bytes _ _ }
  · rw [mem₆, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cSt),
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint cSt), h.blk, stS]
  · rw [mem₆]
    refine ((h.frame.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  · have hne := preserved_ne hr
    rw [keep r hne.2.2.1 hne.2.2.2.1 h4 hne.2.2.2.2 hlr, h.keep r hne.2.2.2.1 h4 h5 hne.2.2.2.2 hlr]

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (FMid s₀) := by
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀) ?_ fun _ h => finArgs_wp hp h)
  have ev : isa.eval .eq s₁ = some (decide (N s₀ = 16)) := by
    show VG.Arm.eval .eq s₁ = _; rw [eval_eq, h₁.z]
  by_cases hL : N s₀ = 16
  · exact WP.ite true (by rw [ev]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h₁)

/-! ## The whole function -/

theorem finalize_wp {s₀ : State} (h0 : finalizeArm.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeArm.post s₀ s' := by
  have hp := FPre.of h0
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have sf := hp.scr_fit
  have cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega)
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call h₁.pre) fun s₂ h₂ => ?_)
  have r5₂ : s₂.gpr .r5 = S s₀ := by rw [h₂.saved .r5 (by simp [preserved]) (by decide), h₁.r5]
  have rdwr₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  have inS : ∀ d, d + 4 ≤ 2176 → InRegions (s₂.rd ++ s₂.wr) (State.addr (S s₀) + BitVec.ofNat 64 d) 4 :=
    fun d hd => by
      rw [rdwr₂]
      obtain ⟨r, hr, hc⟩ := in_of_cov (hp.cS (d := d) (n := 4) hd)
      exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [show ([.ldr .r4 .r5 2064, .ldr .lr .r5 2072, .ldr .r5 .r5 2068] : List Instr) =
    [(.r4, 2064), (.lr, 2072)].map (fun (p : Reg × Nat) => Instr.ldr p.1 .r5 p.2) ++ [.ldr .r5 .r5 2068] from rfl]
  refine Spill.restoreList_ok [(.r4, 2064), (.lr, 2072)] s₂ _ (by decide) (fun p hp' => ?_)
    fun s₃ ld₃ ho₃ m₃ rd₃ wr₃ sp₃ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2076 ∧ p.1 ≠ .r5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl <;> decide
    exact ⟨hb.2.2, by omega, by rw [r5₂]; omega, by rw [r5₂]; exact inS _ (by omega)⟩
  refine wp_ldr (a := State.addr (S s₀) + BitVec.ofNat 64 2068) (by decide)
    (by rw [ho₃ _ (by decide), r5₂]; exact addr_add (by omega))
    (by rw [rd₃, wr₃]; exact inS _ (by decide)) fun s₄ u₄ => WP.block_nil ?_
  -- The slots, which nothing after the save writes.
  have slot : ∀ r d, (r, d) ∈ fsaved → s₂.mem.readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hd : 2064 ≤ d ∧ d + 4 ≤ 2076 := by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hrd
      omega
    rw [h₂.frame.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · rw [cA]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega))
        · exact Offset.disjoint_base _ (by omega) (by omega)
        · rw [below, h₁.sp]; exact hp.b_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
      h₁.frame.readW (r := ⟨State.addr (S s₀) + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact Offset.disjoint _ (by omega) (by omega) (by omega)
        · exact hp.st_scr.symm.sub_left (Offset.sub_base _ (by omega))) (by decide),
      fsMem_slot s₀ hrd]
  have sch : Spec.Aes.bytesAt s₁.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀)) (16 * (R s₀ + 1)) := by
    have f : Frame [scrR s₀, stR s₀] s₀.mem s₁.mem :=
      (((fsMem_frame s₀).mono (by simp)).trans (h₁.frame.sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
        · exact ⟨stR s₀, by simp, fun _ h => h⟩))
    exact Proof.Cmac.bytesAt_frame f (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega))
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))) (by omega)
  refine ⟨⟨fun r hr => ?_, by rw [u₄.sp, sp₃, h₂.sp, h₁.sp]⟩, ?_⟩
  · by_cases h4 : r = .r4
    · subst h4; rw [u₄.other _ (by decide), ld₃ (.r4, 2064) (by simp), r5₂, slot .r4 2064 (by decide)]
    by_cases h5 : r = .r5
    · subst h5; rw [u₄.gpr, m₃, slot .r5 2068 (by decide)]
    by_cases hlr : r = .lr
    · subst hlr; rw [u₄.other _ (by decide), ld₃ (.lr, 2072) (by simp), r5₂, slot .lr 2072 (by decide)]
    rw [u₄.other _ h5, ho₃ _ (by simp [h4, hlr]), h₂.saved r hr hlr, h₁.keep r hr h4 h5 hlr]
  · intro hk msg hm hne hst
    have hk' : Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 240) 32 =
        (Spec.Cmac.subkeys (ciph s₀) 16).1 ++ (Spec.Cmac.subkeys (ciph s₀) 16).2 := hk
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk'
    show Spec.Aes.bytesAt s₄.mem (State.addr (St s₀)) 16 = _
    rw [u₄.mem, m₃, h₂.out, sch, cA, h₁.blk, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.Arm
