import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec

/-! Untrusted: save the caller's registers and prepare the scalar operands. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, 32⟩]
  wr : s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x4, 8192⟩]
  r_sc : (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  k_sc : (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  s_sc : (⟨s.gpr .x3, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩
  nowrap : (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64

structure MulAddReady (s₀ s : State) : Prop where
  base : s.gpr .x0 = s₀.gpr .x4
  out : s.gpr .x19 = s₀.gpr .x0
  sp : s.sp = s₀.sp
  preserved : ∀ r ∈ [Reg.x25, .x26, .x27, .x28, .x30], s.gpr r = s₀.gpr r
  value : val4 (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7) = fe s₀.mem (s₀.gpr .x1) 0
  left : fe s.mem (s₀.gpr .x4) 64 = fe s₀.mem (s₀.gpr .x2) 0
  right : fe s.mem (s₀.gpr .x4) 96 = fe s₀.mem (s₀.gpr .x3) 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved (s₀.gpr .x4) s₀.gpr s.mem
  frame : Frame [⟨s₀.gpr .x4, 8192⟩] s₀.mem s.mem

theorem mulAddArgs_ok (s : State) :
    WP isa (.block [mov .x19 .x0, mov .x0 .x4]) s fun t =>
      t.gpr .x19 = s.gpr .x0 ∧ t.gpr .x0 = s.gpr .x4 ∧ Keeps [.x19, .x0] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, mov, read_x,
    show (0 : Nat) < 4096 from by decide, RegUpd.gpr_write, BitVec.setWidth_eq, BitVec.add_zero,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem mulAddSetup_ok {s : State} (hs : MulAddPre s) :
    WP isa (.block mulAddSetup) s (MulAddReady s) := by
  have hw : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [show mulAddSetup = mulAddSave ++ (([mov .x19 .x0, mov .x0 .x4] :
    List Instr) ++ (copyScalar .x2 64 ++ (copyScalar .x3 96 ++ loadWords .x1))) by
    simp only [mulAddSetup, List.append_assoc], WP.block_append_iff]
  refine WP.mono (mulAddSave_ok rfl hw) fun s₁ ⟨g₁, rd₁, wr₁, sp₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulAddArgs_ok s₁) fun s₂ ⟨out₂, base₂, k₂⟩ => ?_
  have hp₂ : s₂.gpr .x0 = s.gpr .x4 := base₂.trans (congrFun g₁ _)
  have hw₂ : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s₂.wr := by rw [k₂.wr, wr₁]; exact hw
  have g₂ : ∀ r, r ∉ [Reg.x19, .x0] → s₂.gpr r = s.gpr r :=
    fun r h => (k₂.gpr r h).trans (congrFun g₁ r)
  have fm₂ : Frame [⟨s.gpr .x4, 8192⟩] s.mem s₂.mem := by
    rw [k₂.mem]; exact scratchFrame o₁ (by decide)
  have hr₂ : ∀ d, d + 8 ≤ 32 → InRegions (s₂.rd ++ s₂.wr) (off (s₂.gpr .x2) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .x2, 32⟩, ?_, ?_⟩
    · rw [k₂.rd, rd₁, hs.rd]; simp
    · rw [g₂ .x2 (by decide)]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (copyScalar_ok ⟨hp₂, hw₂, hs.nowrap⟩ .x2 (by decide) hr₂ 64 (by constructor <;> decide))
    fun s₃ ⟨v₃, g₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  have hp₃ : s₃.gpr .x0 = s.gpr .x4 := (g₃ _ (by decide)).trans hp₂
  have hw₃ : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s₃.wr := wr₃ ▸ hw₂
  have fm₃ := fm₂.trans (scratchFrame o₃ (by decide))
  have rcx₃ : s₃.gpr .x3 = s.gpr .x3 := (g₃ _ (by decide)).trans (g₂ _ (by decide))
  have hr₃ : ∀ d, d + 8 ≤ 32 → InRegions (s₃.rd ++ s₃.wr) (off (s₃.gpr .x3) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .x3, 32⟩, ?_, ?_⟩
    · rw [rd₃, k₂.rd, rd₁, hs.rd]; simp
    · rw [rcx₃]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (copyScalar_ok ⟨hp₃, hw₃, hs.nowrap⟩ .x3 (by decide) hr₃ 96 (by constructor <;> decide))
    fun s₄ ⟨v₄, g₄, rd₄, wr₄, sp₄, o₄⟩ => ?_
  have fm₄ := fm₃.trans (scratchFrame o₄ (by decide))
  have rsi₄ : s₄.gpr .x1 = s.gpr .x1 :=
    (g₄ _ (by decide)).trans ((g₃ _ (by decide)).trans (g₂ _ (by decide)))
  have hr₄ : ∀ d, d + 8 ≤ 32 → InRegions (s₄.rd ++ s₄.wr) (off (s₄.gpr .x1) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .x1, 32⟩, ?_, ?_⟩
    · rw [rd₄, rd₃, k₂.rd, rd₁, hs.rd]; simp
    · rw [rsi₄]; exact Offset.contains_base _ hd (by omega)
  refine WP.mono (loadWords_ok s₄ .x1 (by decide) hr₄) fun t ⟨vt, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kt.gpr _ (by decide), g₄ _ (by decide)]; exact hp₃
  · rw [kt.gpr _ (by decide), g₄ _ (by decide), g₃ _ (by decide), out₂, g₁]
  · rw [kt.sp, sp₄, sp₃, k₂.sp, sp₁]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      rw [kt.gpr _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]
  · rw [vt, rsi₄, fe_frame fm₄ hs.r_sc]
  · rw [kt.mem, o₄.fe (by decide) (by decide), v₃, g₂ _ (by decide), fe_frame fm₂ hs.k_sc]
  · rw [kt.mem, v₄, rcx₃, fe_frame fm₃ hs.s_sc]
  · rw [kt.rd, rd₄, rd₃, k₂.rd, rd₁]
  · rw [kt.wr, wr₄, wr₃, k₂.wr, wr₁]
  · have sv₂ : Saved (s.gpr .x4) s.gpr s₂.mem := by rw [k₂.mem]; exact sv₁
    rw [kt.mem]; exact (sv₂.outside o₃ (by decide)).outside o₄ (by decide)
  · rw [kt.mem]; exact fm₄

end VG.Proof.Ed25519.AArch64
