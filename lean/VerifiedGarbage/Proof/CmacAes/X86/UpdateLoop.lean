import VerifiedGarbage.Proof.CmacAes.X86.Update

/-!
# AES-CMAC on x86: the loop of `vg_cmac_aes_update`

One block keeps the loop invariant (`body_ok`): the counter block is `C ⊕ Mᵢ`
and the state is zeroed (`Cmac.chainMem4`), the call of `vg_aes_ctr32` leaves
`CIPH_K(C ⊕ Mᵢ)` in the state, and ZF is set once `esi` reaches `data + 16 n`
(`adv_zf`).
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_cmp eval_ne)

theorem take_succ_blks (s₀ : State) {k : Nat} (hk : k < N s₀) :
    (blks s₀).take (k + 1) =
      (blks s₀).take k ++ [Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16] := by
  rw [List.take_add_one, List.getElem?_eq_getElem (by simp [Spec.Cmac.blocksAt]; omega)]
  simp [Spec.Cmac.blocksAt]

/-! ## Memory outside the writable regions -/

section
variable {s₀ : State} (hp : UPre s₀)
include hp

theorem UPre.sched_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) :
    Spec.Aes.bytesAt m ((W s₀).setWidth 64) (16 * (R s₀ + 1)) =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64) (16 * (R s₀ + 1)) := by
  have hR : 16 * (R s₀ + 1) ≤ 240 := by rcases hp.rounds with h | h | h <;> omega
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.sch_st.sub_left (Region.sub_prefix hR)
  · exact hp.sch_scr.sub_left (Region.sub_prefix hR)
  · exact hp.b_sch.symm.sub_left (Region.sub_prefix hR)

theorem UPre.block_bytes {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {k : Nat} (hk : k < N s₀) :
    Spec.Aes.bytesAt m ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 =
      Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) 16 := by
  refine Proof.Cmac.bytesAt_frame hf (fun r hr => ?_) (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hp.data_st.sub_left (UPre.data_sub hk)
  · exact hp.data_scr.sub_left (UPre.data_sub hk)
  · exact hp.b_data.symm.sub_left (UPre.data_sub hk)

end

theorem UPre.big_of {s₀ : State} {m : Mem}
    (hf : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) m) : Frame (Big s₀) s₀.mem m :=
  (savedMem_big s₀).trans (hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
    · exact ⟨scrR s₀, by simp, Region.sub_prefix (by decide)⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩)

/-! ## The end of a block -/

theorem dbl4 (n : BitVec 32) : n + n + (n + n) + (n + n + (n + n)) + (n + n + (n + n) + (n + n + (n + n))) =
    BitVec.ofNat 32 (16 * n.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem adv_zf {D n : BitVec 32} {k : Nat} (hk : k < n.toNat) (hfit : D.toNat + 16 * n.toNat ≤ 2 ^ 32) :
    (D + BitVec.ofNat 32 (16 * k) + 16 - ((n + n + (n + n) + (n + n + (n + n)) +
      (n + n + (n + n) + (n + n + (n + n)))) + D) == 0) = decide (k + 1 = n.toNat) := by
  rw [dbl4, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow]
  have := D.isLt
  have h16 : (16 : BitVec 32).toNat = 16 := rfl
  have h0 : (0 : BitVec 32).toNat = 0 := rfl
  omega

theorem advance_eq : advance = .alu .add .esi (.imm 16) :: .mov .eax (argOp 4) :: .alu .add .eax (.reg .eax) ::
    .alu .add .eax (.reg .eax) :: .alu .add .eax (.reg .eax) :: .alu .add .eax (.reg .eax) ::
    .alu .add .eax (argOp 3) :: .alu .cmp .esi (.reg .eax) :: [] := rfl

theorem advance_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State}
    (hesi : s.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k)) (hesp : s.gpr .esp = E s₀)
    (hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i) (hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr) :
    WP isa (.block advance) s fun s' => s'.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * (k + 1)) ∧
      s'.gpr .esp = E s₀ ∧ (∀ r, r ≠ .eax → r ≠ .esi → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  rw [advance_eq]
  refine wp_addi fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), hesp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 4 (by decide)) fun s₂ u₂ => ?_
  refine wp_add fun s₃ u₃ => wp_add fun s₄ u₄ => wp_add fun s₅ u₅ => wp_add fun s₆ u₆ => ?_
  refine wp_addArg (s₀ := s₀)
    (by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hesp])
    (by rw [u₆.rd, u₆.wr, u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
        exact hp.arg_in (by decide))
    (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hargs 3 (by decide)) fun s₇ u₇ => ?_
  refine wp_cmp fun s₈ f₈ _ z₈ => WP.block_nil ⟨?_, ?_, fun r h₁ h₂ => ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hesi, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      Offset.add_add_eq _ (c := 16 * (k + 1)) (by omega)]
  · rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hesp]
  · rw [f₈.gpr, u₇.other _ h₁, u₆.other _ h₁, u₅.other _ h₁, u₄.other _ h₁, u₃.other _ h₁, u₂.other _ h₁,
      u₁.other _ h₂]
  · rw [f₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  · rw [f₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  · rw [z₈, u₇.gpr, u₇.other _ (by decide), u₆.gpr, u₆.other _ (by decide), u₅.gpr, u₅.other _ (by decide),
      u₄.gpr, u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₂.other _ (by decide), u₁.gpr, hesi]
    exact congrArg some (adv_zf hk hp.data_fit)

/-! ## One block -/

/-- The counter block's address. -/
abbrev Cb (s₀ : State) : BitVec 32 := S s₀ + BitVec.ofNat 32 2048

/-- What the code before the call leaves. -/
structure BodyA (s₀ : State) (k : Nat) (s s₁ : State) : Prop where
  pre : CtrPre s₁ (W s₀) (Cb s₀) (St s₀) (S s₀) (R s₀)
  esi : s₁.gpr .esi = s.gpr .esi
  esp : s₁.gpr .esp = s.gpr .esp
  mem : s₁.mem = Proof.Cmac.chainMem4 s.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 2048) ((St s₀).setWidth 64)
    ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k))
  rd : s₁.rd = s.rd
  wr : s₁.wr = s.wr

theorem ctrArgs_eq : ctrArgs = [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .edx (.reg .ebp),
    .alu .add .edx (.imm (BitVec.ofNat 32 2048)), .mov .edi (.imm 1)] := rfl

theorem chainIn_eq : chainIn = .mov .ebx (argOp 2) :: .mov .ebp (argOp 5) ::
    (xor4 .ebx .esi .ebp 0 0 2048 ++ (zero4 .ebx 0 ++ ctrArgs)) := rfl

theorem bodyA_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block chainIn) s (BodyA s₀ k s) := by
  have hRegs : s.rd ++ s.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have hW : s.wr = [stR s₀, scrR s₀] := by rw [h.wr, hp.wr]
  have hsc := hp.scr_fit
  have hst := hp.st_fit
  have hdf := hp.data_fit
  have qN := hp.dataN hk
  have big := UPre.big_of h.frame
  have hargs : ∀ i < 6, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi => hp.arg_keep big hi
  rw [chainIn_eq]
  refine wp_arg (s₀ := s₀) h.esp (by rw [hrw]; exact hp.arg_in (by decide)) (hargs 2 (by decide))
    fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), h.esp]) (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem]; exact hargs 5 (by decide)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebx = St s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have p₂ : s₂.gpr .ebp = S s₀ := u₂.gpr
  have i₂ : s₂.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  have rw₂ : s₂.rd ++ s₂.wr = [schR s₀, dataR s₀, argsR s₀, stR s₀, scrR s₀] := by
    rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hRegs]
  have w₂ : s₂.wr = [stR s₀, scrR s₀] := by rw [u₂.wr, u₁.wr, hW]
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₂]; omega) (by rw [i₂, qN]; omega) (by rw [p₂]; omega) ?_ ?_ ?_ fun s₃ g₃ => ?_
  · rw [b₂, add0, rw₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  · rw [i₂, add0, show (Dp s₀ + BitVec.ofNat 32 (16 * k)).setWidth 64 = addr (Dp s₀) (16 * k) from rfl,
      hp.dataA hk, rw₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨dataR s₀, by simp, 16 * k, rfl, by simp; omega⟩
  · rw [p₂, w₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
  have b₃ : s₃.gpr .ebx = St s₀ := by rw [g₃.gpr _ (by decide) (by decide), b₂]
  refine zero4_ok (by decide) (by rw [b₃]; omega) ?_ fun s₄ g₄ m₄ rd₄ wr₄ => ?_
  · rw [b₃, add0, g₃.wr, w₂]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
  have esp₄ : s₄.gpr .esp = E s₀ := by
    rw [g₄ _ (by decide), g₃.gpr _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esp]
  have rd₄' : s₄.rd = s.rd := by rw [rd₄, g₃.rd, u₂.rd, u₁.rd]
  have wr₄' : s₄.wr = s.wr := by rw [wr₄, g₃.wr, u₂.wr, u₁.wr]
  have mem₄ : s₄.mem = Proof.Cmac.chainMem4 s.mem ((S s₀).setWidth 64 + BitVec.ofNat 64 2048)
      ((St s₀).setWidth 64) ((Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k)) := by
    rw [m₄, b₃, add0, g₃.mem, p₂, b₂, i₂, add0, add0,
      show (Dp s₀ + BitVec.ofNat 32 (16 * k)).setWidth 64 = addr (Dp s₀) (16 * k) from rfl, hp.dataA hk,
      u₂.mem, u₁.mem]
    rfl
  have hargs₄ : ∀ i < 6, s₄.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
    intro i hi
    rw [mem₄]
    refine (Proof.Cmac.chainMem4_frame _ _ _ _).readW (Region.contains_self _ _) (fun r hr => ?_) (by decide) |>.trans
      (hargs i hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (hp.args_scr.sub_left (hp.arg_sub hi)).sub_right (UPre.scr_sub (by decide))
    · exact hp.args_st.sub_left (hp.arg_sub hi)
  rw [ctrArgs_eq]
  refine wp_arg (s₀ := s₀) esp₄ (by rw [rd₄', wr₄', hrw]; exact hp.arg_in (by decide)) (hargs₄ 0 (by decide))
    fun s₅ u₅ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₅.other _ (by decide), esp₄])
    (by rw [u₅.rd, u₅.wr, rd₄', wr₄', hrw]; exact hp.arg_in (by decide))
    (by rw [u₅.mem]; exact hargs₄ 1 (by decide)) fun s₆ u₆ => ?_
  refine wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_movi fun s₉ u₉ => WP.block_nil ?_
  have keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₉.gpr r = s₄.gpr r := fun r ha hc hd hi => by
    rw [u₉.other _ hi, u₈.other _ hd, u₇.other _ hd, u₆.other _ hc, u₅.other _ ha]
  have p₄ : s₄.gpr .ebp = S s₀ := by rw [g₄ _ (by decide), g₃.gpr _ (by decide) (by decide), p₂]
  have b₄ : s₄.gpr .ebx = St s₀ := by rw [g₄ _ (by decide), b₃]
  have sp₉ : s₉.gpr .esp = E s₀ := by rw [keep _ (by decide) (by decide) (by decide) (by decide), esp₄]
  have rd₉ : s₉.rd = s.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄']
  have wr₉ : s₉.wr = s.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄']
  have mem₉ : s₉.mem = s₄.mem := by rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem]
  have hb : below (s₉.gpr .esp) 28 = stkR s₀ := by rw [sp₉]; exact hp.below_eq
  have cA : (Cb s₀).setWidth 64 = (S s₀).setWidth 64 + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have cSt : (⟨(Cb s₀).setWidth 64, 16⟩ : Region).Disjoint (stR s₀) := by
    rw [cA]; exact hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  refine ⟨⟨?_, ?_, ?_, ?_, u₉.gpr, ?_, hp.rounds, by rw [sp₉]; exact hp.esp28, ?_, hp.sch_st, ?_, cSt,
    ?_, ?_, by rw [hb]; exact hp.b_sch, ?_, by rw [hb]; exact hp.b_st, ?_, hp.sch_fit, ?_, hp.st_fit, ?_, ?_, ?_,
    ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
  · rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr]; exact arg_ofNat s₀ 1
  · rw [u₉.other _ (by decide), u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), p₄]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), b₄]
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), p₄]
  · rw [cA]; exact hp.sch_scr.sub_right (UPre.scr_sub (by decide))
  · exact hp.sch_scr.sub_right (Region.sub_prefix (by decide))
  · rw [cA]; exact Offset.disjoint_base _ (by decide) (by omega)
  · exact hp.st_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hb, cA]; exact hp.b_scr.sub_right (UPre.scr_sub (by decide))
  · rw [hb]; exact hp.b_scr.sub_right (Region.sub_prefix (by decide))
  · rw [hp.scrN (by decide)]; omega
  · omega
  · rw [rd₉, wr₉, hRegs]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨schR s₀, by simp, 0, by simp, by simp⟩
  · rw [wr₉, hW, cA]
    refine Covers.of_sub fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨scrR s₀, by simp, 2048, rfl, by simp⟩
    · exact ⟨stR s₀, by simp, 0, by simp, by simp⟩
    · exact ⟨scrR s₀, by simp, 0, by simp, by simp⟩
  · rw [mem₉, mem₄]; exact Proof.Cmac.chainMem4_state _ _ _ _
  · rw [keep _ (by decide) (by decide) (by decide) (by decide), g₄ _ (by decide), g₃.gpr _ (by decide) (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide)]
  · rw [sp₉, h.esp]
  · rw [mem₉, mem₄]
  · exact rd₉
  · exact wr₉

theorem body_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa body s fun s' => LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (k + 1 = N s₀)) := by
  have hdf := hp.data_fit
  refine WP.seq (WP.mono (bodyA_wp hp hk h) fun s₁ a => ?_)
  refine WP.seq (WP.mono (ctr_call a.pre) fun s₂ h₂ => ?_)
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [a.esp, h.esp]
  have hb : below (s₁.gpr .esp) 28 = stkR s₀ := by rw [esp₁]; exact hp.below_eq
  have cA : (Cb s₀).setWidth 64 = (S s₀).setWidth 64 + BitVec.ofNat 64 2048 := hp.scrA (by decide)
  have f₁ : Frame [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩, stR s₀] s.mem s₁.mem := by
    rw [a.mem]; exact Proof.Cmac.chainMem4_frame _ _ _ _
  have f₂ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s₁.mem s₂.mem := by
    have fr := h₂.frame
    rw [hb, cA] at fr
    exact fr.sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
      · exact ⟨stR s₀, by simp, fun _ h => h⟩
      · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Region.sub_prefix (by decide)⟩
      · exact ⟨stkR s₀, by simp, fun _ h => h⟩
  have f₁' : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] s.mem s₁.mem := f₁.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨⟨(S s₀).setWidth 64, 2064⟩, by simp, Offset.sub_base _ (by decide)⟩
    · exact ⟨stR s₀, by simp, fun _ h => h⟩
  have fr₂ : Frame [stR s₀, ⟨(S s₀).setWidth 64, 2064⟩, stkR s₀] (savedMem s₀) s₂.mem :=
    (h.frame.trans f₁').trans f₂
  have big₂ := UPre.big_of fr₂
  have big₁ := UPre.big_of (h.frame.trans f₁')
  have esi₂ : s₂.gpr .esi = Dp s₀ + BitVec.ofNat 32 (16 * k) := by
    rw [h₂.saved .esi (by simp [calleeSaved]), a.esi, h.esi]
  have esp₂ : s₂.gpr .esp = E s₀ := by rw [h₂.saved .esp (by simp [calleeSaved]), esp₁]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [h₂.rd, h₂.wr, a.rd, a.wr, h.rd, h.wr]
  refine WP.mono (advance_wp hp hk esi₂ esp₂ (fun i hi => hp.arg_keep big₂ hi) rw₂) fun s₃ ⟨esi₃, esp₃, _, mem₃,
    rd₃, wr₃, zf₃⟩ => ⟨⟨esi₃, esp₃, by rw [rd₃, h₂.rd, a.rd, h.rd], by rw [wr₃, h₂.wr, a.wr, h.wr],
      by rw [mem₃]; exact fr₂, ?_⟩, zf₃⟩
  have cst : (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint (stR s₀) :=
    hp.st_scr.symm.sub_left (UPre.scr_sub (by decide))
  have cq : (⟨(S s₀).setWidth 64 + BitVec.ofNat 64 2048, 16⟩ : Region).Disjoint
      ⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 (16 * k), 16⟩ :=
    (hp.data_scr.symm.sub_left (UPre.scr_sub (by decide))).sub_right (UPre.data_sub hk)
  have out := h₂.out
  rw [UPre.sched_bytes hp big₁, cA, a.mem, Proof.Cmac.chainMem4_counter _ cst cq, h.state,
    UPre.block_bytes hp (UPre.big_of h.frame) hk] at out
  rw [mem₃, out, take_succ_blks s₀ hk, Proof.Cmac.chain_append, Proof.Cmac.chain_single]

theorem loop_ok {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.loop body .ne) s (LInv s₀ (N s₀)) := by
  refine WP.loop (M := isa) (body := body) (c := .ne) (Q := LInv s₀ (N s₀))
    (fun (n : Nat) (t : State) => ∃ j, n = N s₀ - j ∧ j < N s₀ ∧ LInv s₀ j t) ?_ (N s₀ - k) s
    ⟨k, rfl, hk, h⟩
  rintro n s ⟨k, rfl, hk, h⟩
  refine WP.mono (body_ok hp hk h) fun s' ⟨h', hz⟩ => ?_
  have ev : isa.eval .ne s' = some !decide (k + 1 = N s₀) := by
    show VG.X86.eval .ne s' = _; rw [eval_ne, hz]; rfl
  by_cases hz' : k + 1 = N s₀
  · left
    refine ⟨by rw [ev]; simp [hz'], ?_⟩
    rwa [← hz']
  · right
    refine ⟨by rw [ev]; simp [hz'], N s₀ - (k + 1), by omega, k + 1, rfl, by omega, h'⟩

end VG.Proof.CmacAes.X86
