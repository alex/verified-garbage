import VerifiedGarbage.Proof.CmacAes.X86.Finalize

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize` is correct

Before the call, the counter block holds `Mₙ ⊕ C`, for the last block `Mₙ` of
§6.2 step 4 and the chaining value `C` at `state`, and the state is zeroed;
the call leaves `CIPH_K(C ⊕ Mₙ)` there, the MAC (`Cmac.macFull_split`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd wp_mov wp_movi wp_addi eval_e)

/-! ## Up to the call -/

/-- What the code before the call leaves. -/
structure FMid (s₀ s : State) : Prop where
  pre : CtrPre s (W s₀) (S s₀ + BitVec.ofNat 32 2048) (St s₀) (S s₀) (R s₀)
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 =
    Spec.Cmac.xor (mn s₀) (Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 16)
  frame : Frame [⟨Ca s₀, 16⟩, stR s₀] (savedMem s₀) s.mem
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finArgs_eq : finArgs = .mov .ebx (argOp 2) :: (xor4 .ebp .ebx .ebp 2048 0 2048 ++ (zero4 .ebx 0 ++ ctrArgs)) :=
  rfl

theorem finArgs_wp {s₀ : State} (hp : FPre s₀) {s : State} (h : BPost s₀ s) :
    WP isa (.block finArgs) s (FMid s₀) := by
  have sf := hp.scr_fit
  have tf := hp.st_fit
  have hR := hp.rounds
  have cA := hp.cA
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have cSt : (⟨Ca s₀, 16⟩ : Region).Disjoint (stR s₀) := hp.st_scr.symm.sub_left (Offset.sub_base _ (by decide))
  have wSt : Covers [stR s₀] s₀.wr := by
    rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  have big : Frame (Big s₀) s₀.mem s.mem :=
    (savedMem_big s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  rw [finArgs_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hp.arg_keep big (by decide))
    fun s₁ u₁ => ?_
  have b₁ : s₁.gpr .ebx = St s₀ := u₁.gpr
  have p₁ : s₁.gpr .ebp = S s₀ := by rw [u₁.other _ (by decide), h.ebp]
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [u₁.rd, u₁.wr, hrw]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [p₁]; omega) (by rw [b₁]; omega) (by rw [p₁]; omega)
    (by
      rw [p₁, rw₁]
      exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
        fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by
      rw [b₁, add0, rw₁]
      exact fun a n hi => wSt a n hi |> fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
    (by rw [p₁, u₁.wr, h.wr]; exact hp.cS (by decide)) fun s₂ g₂ => ?_
  have b₂ : s₂.gpr .ebx = St s₀ := by rw [g₂.gpr _ (by decide) (by decide), b₁]
  refine zero4_ok (by decide) (by rw [b₂]; omega) (by rw [b₂, add0, g₂.wr, u₁.wr, h.wr]; exact wSt)
    fun s₃ g₃ m₃ rd₃ wr₃ => ?_
  have esp₃ : s₃.gpr .esp = E s₀ := by
    rw [g₃ _ (by decide), g₂.gpr _ (by decide) (by decide), u₁.other _ (by decide), h.esp]
  have rd₃' : s₃.rd = s₀.rd := by rw [rd₃, g₂.rd, u₁.rd, h.rd]
  have wr₃' : s₃.wr = s₀.wr := by rw [wr₃, g₂.wr, u₁.wr, h.wr]
  have mem₃ : s₃.mem = Proof.Cmac.zero4 (Proof.Cmac.xor4Mem s.mem (Ca s₀) (Ca s₀) ((St s₀).setWidth 64))
      ((St s₀).setWidth 64) := by
    rw [m₃, b₂, add0, g₂.mem, p₁, b₁, add0, u₁.mem]
  have fr₃ : Frame [⟨Ca s₀, 16⟩, stR s₀] (savedMem s₀) s₃.mem := by
    rw [mem₃]
    exact ((h.frame.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)).mono (by simp)).trans
      ((Proof.Cmac.frame_store4 _ _ _ _ _).mono (by simp))
  have big₃ : Frame (Big s₀) s₀.mem s₃.mem :=
    (savedMem_big s₀).trans (fr₃.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩)
  rw [ctrArgs_eq]
  refine wp_arg (s₀ := s₀) esp₃ (by rw [rd₃', wr₃']; exact hp.arg_in (by decide)) (hp.arg_keep big₃ (by decide))
    fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), esp₃])
    (by rw [u₄.rd, u₄.wr, rd₃', wr₃']; exact hp.arg_in (by decide))
    (by rw [u₄.mem]; exact hp.arg_keep big₃ (by decide)) fun s₅ u₅ => ?_
  refine wp_mov fun s₆ u₆ => wp_addi fun s₇ u₇ => wp_movi fun s₈ u₈ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₈.gpr r = s₃.gpr r := fun r ha hc hd hi => by
    rw [u₈.other _ hi, u₇.other _ hd, u₆.other _ hd, u₅.other _ hc, u₄.other _ ha]
  have p₃ : s₃.gpr .ebp = S s₀ := by rw [g₃ _ (by decide), g₂.gpr _ (by decide) (by decide), p₁]
  have b₃ : s₃.gpr .ebx = St s₀ := by rw [g₃ _ (by decide), b₂]
  have sp₈ : s₈.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₃]
  have rd₈ : s₈.rd = s₀.rd := by rw [u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, rd₃']
  have wr₈ : s₈.wr = s₀.wr := by rw [u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, wr₃']
  have mem₈ : s₈.mem = s₃.mem := by rw [u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem]
  have hb : below (s₈.gpr .esp) 28 = stkR s₀ := by rw [sp₈]; exact hp.below_eq
  have stS : Spec.Aes.bytesAt s.mem ((St s₀).setWidth 64) 16 =
      Spec.Aes.bytesAt s₀.mem ((St s₀).setWidth 64) 16 :=
    Proof.Cmac.bytesAt_frame16 ((savedMem_frame s₀).trans (h.frame.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩)) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.st_scr
  refine ⟨⟨?_, ?_, ?_, ?_, u₈.gpr, ?_, hR, by rw [sp₈]; exact hp.esp28, ?_,
    hp.key_st.sub_left (Region.sub_prefix (by decide)),
    (hp.key_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)),
    by rw [cA]; exact cSt, by rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega),
    hp.st_scr.sub_right (Region.sub_prefix (by decide)),
    by rw [hb]; exact hp.b_key.sub_right (Region.sub_prefix (by decide)),
    by rw [hb, cA]; exact hp.b_scr.sub_right (Offset.sub_base _ (by decide)), by rw [hb]; exact hp.b_st,
    by rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide)), by have := hp.key_fit; omega, ?_, tf,
    by omega, ?_, ?_, ?_⟩, ?_, ?_, sp₈, rd₈, wr₈⟩
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]
  · rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]; exact arg_ofNat s₀ 1
  · rw [u₈.other _ (by decide), u₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), p₃]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₃]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₃]
  · rw [cA]; exact (hp.ca_key (d := 0) (n := 240) (by decide)).symm |> fun d => by simpa using d
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
      Nat.mod_eq_of_lt (by omega)]; omega
  · rw [rd₈, wr₈, hp.rd]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨keyR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₈, hp.wr, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₈, mem₃]; exact Proof.Cmac.zero4_bytes _ _
  · rw [mem₈, mem₃, Proof.Cmac.zero4, Proof.Cmac.bytesAt_frame16 (Proof.Cmac.frame_store4 _ _ _ _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cSt),
      Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _) (Proof.Cmac.Sep4.of_disjoint cSt), h.blk, stS]
  · rw [mem₈]; exact fr₃

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (FMid s₀) := by
  refine WP.seq (WP.mono (finSave_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (Q := BPost s₀) ?_ fun _ h => finArgs_wp hp h)
  have ev : isa.eval .e s₁ = some (decide (N s₀ = 16)) := by
    show VG.X86.eval .e s₁ = _; rw [eval_e, h₁.zf]
  by_cases hL : N s₀ = 16
  · exact WP.ite true (by rw [ev]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h₁)

/-! ## The whole function -/

theorem finalize_wp {s₀ : State} (h0 : finalizeX86.pre s₀) :
    WP isa finalize s₀ fun s' => abiPreserved s₀ s' ∧ finalizeX86.post s₀ s' := by
  have hp := FPre.of h0
  have hR := hp.rounds
  have hRb : 16 * (R s₀ + 1) ≤ 240 := by rcases hR with h | h | h <;> omega
  have hsc : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := hp.scr_fit
  have cA := hp.cA
  unfold finalize
  refine WP.seq (WP.mono (finPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (ctr_call h₁.pre) fun s₂ h₂ => ?_)
  have hb : below (s₁.gpr .esp) 28 = stkR s₀ := by rw [h₁.esp]; exact hp.below_eq
  have f₁ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s₁.mem :=
    h₁.frame.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
  have f₂ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA] at fr
    refine f₁.trans (fr.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have big₁ := UPre.big_of f₁
  have big₂ := UPre.big_of f₂
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [h₂.saved .esp (by simp [calleeSaved]), h₁.esp]
  have rdwr₂ : s₂.rd ++ s₂.wr = [keyR s₀, lastR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr, hp.rd, hp.wr]; rfl
  have hrw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]
  have sl : ∀ r d, (r, d) ∈ saved → s₂.mem.readW ((S s₀).setWidth 64 + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
    intro r d hrd
    have hb := saved_bound _ hrd
    rw [f₂.readW (r := ⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.st_scr.symm.sub_left (UPre.scr_sub (by omega))
      · exact Offset.disjoint_base _ hb.1 (by omega)
      · exact hp.b_scr.symm.sub_left (UPre.scr_sub (by omega))) (by decide), savedMem_slot s₀ hrd]
  have sch : Spec.Aes.bytesAt s₁.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) :=
    Proof.Cmac.bytesAt_frame big₁ (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.key_st.sub_left (Region.sub_prefix (by omega))
      · exact hp.key_scr.sub_left (Region.sub_prefix (by omega))
      · exact hp.b_key.symm.sub_left (Region.sub_prefix (by omega))) (by omega)
  rw [restore_eq]
  refine wp_arg (s₀ := s₀) esp₂ (by rw [hrw₂]; exact hp.arg_in (by decide)) (hp.arg_keep big₂ (by decide))
    fun s₃ u₃ => ?_
  refine restoreList_ok saved s₃ _ saved_nodup (fun p hp' => ?_) fun s₄ ld₄ ho₄ m₄ rd₄ wr₄ => WP.block_nil ?_
  · have hb := saved_bound p hp'
    rw [u₃.gpr, u₃.rd, u₃.wr, rdwr₂]
    exact ⟨saved_ne_eax p hp', by omega, ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩⟩
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [ld₄ (.ebx, 2064) (by decide), u₃.gpr, u₃.mem, sl .ebx 2064 (by decide)]
    · rw [ld₄ (.esi, 2068) (by decide), u₃.gpr, u₃.mem, sl .esi 2068 (by decide)]
    · rw [ld₄ (.edi, 2072) (by decide), u₃.gpr, u₃.mem, sl .edi 2072 (by decide)]
    · rw [ld₄ (.ebp, 2076) (by decide), u₃.gpr, u₃.mem, sl .ebp 2076 (by decide)]
    · rw [ho₄ _ (by decide), u₃.other _ (by decide), esp₂]
  · rw [m₄, u₃.mem]
    have rs : (retR s₀).Disjoint (stkR s₀) := by
      have := Offset.disjoint_below_above ((E s₀).setWidth 64) (m := 28) (a := 0) (l := 4) (by decide)
      rw [add0] at this
      exact this.symm
    exact big₂.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact hp.ret_st
      · exact hp.ret_scr
      · exact rs) (by decide)
  · intro hk msg hm hne hst
    have hk' : Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 240) 32 =
        (Spec.Cmac.subkeys (ciph s₀) 16).1 ++ (Spec.Cmac.subkeys (ciph s₀) 16).2 := hk
    obtain ⟨e1, e2⟩ := Proof.Cmac.k1k2 (Proof.Cmac.subkeys_aes_length _ _) hk'
    show Spec.Aes.bytesAt s₄.mem ((St s₀).setWidth 64) 16 = _
    rw [m₄, u₃.mem, h₂.out, sch, cA, h₁.blk, mn, e1, e2, hst,
      Proof.Cmac.macFull_split _ hm (by rw [Proof.Cmac.bytesAt_length]; exact hp.len)
        (by rw [Proof.Cmac.bytesAt_length]; exact hne), Proof.Cmac.xor_comm]

end VG.Proof.CmacAes.X86
