import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddCodec

/-! Save the caller's registers and prepare the scalar operands. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.X25519.X86_64
open VG.Proof.X25519.X86_64

structure MulAddPre (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .rsi, 32⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 32⟩]
  wr : s.wr = [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .r8, 8192⟩]
  r_sc : (⟨s.gpr .rsi, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  k_sc : (⟨s.gpr .rdx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  s_sc : (⟨s.gpr .rcx, 32⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  ret_out : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .rdi, 32⟩
  ret_sc : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint ⟨s.gpr .r8, 8192⟩
  nowrap : (s.gpr .r8).toNat + 8192 ≤ 2 ^ 64

structure MulAddReady (s₀ s : State) : Prop where
  base : s.gpr .rdi = s₀.gpr .r8
  out : s.gpr .rbx = s₀.gpr .rdi
  rsp : s.gpr .rsp = s₀.gpr .rsp
  value : val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) = fe s₀.mem (s₀.gpr .rsi) 0
  left : fe s.mem (s₀.gpr .r8) 64 = fe s₀.mem (s₀.gpr .rdx) 0
  right : fe s.mem (s₀.gpr .r8) 96 = fe s₀.mem (s₀.gpr .rcx) 0
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  saved : Saved (s₀.gpr .r8) s₀.gpr s.mem
  frame : Frame [⟨s₀.gpr .r8, 8192⟩] s₀.mem s.mem

theorem mulAddArgs_ok (s : State) :
    WP isa (.block [.mov .rbx (.reg .rdi), .mov .rdi (.reg .r8)]) s fun t =>
      t.gpr .rbx = s.gpr .rdi ∧ t.gpr .rdi = s.gpr .r8 ∧ Keeps [.rbx, .rdi] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem mulAddSetup_ok {s : State} (hs : MulAddPre s) :
    WP isa (.block mulAddSetup) s (MulAddReady s) := by
  have hw : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [show mulAddSetup = mulAddSave ++ (([.mov .rbx (.reg .rdi), .mov .rdi (.reg .r8)] :
    List Instr) ++ (copyScalar .rdx 64 ++ (copyScalar .rcx 96 ++ loadScalar))) by
    simp only [mulAddSetup, List.append_assoc], WP.block_append_iff]
  refine WP.mono (mulAddSave_ok rfl hw) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mulAddArgs_ok s₁) fun s₂ ⟨out₂, base₂, k₂⟩ => ?_
  have hp₂ : s₂.gpr .rdi = s.gpr .r8 := base₂.trans (congrFun g₁ _)
  have hw₂ : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s₂.wr := by rw [k₂.2.2.2, wr₁]; exact hw
  have g₂ : ∀ r, r ∉ [Reg.rbx, .rdi] → s₂.gpr r = s.gpr r :=
    fun r h => (k₂.1 r h).trans (congrFun g₁ r)
  have fm₂ : Frame [⟨s.gpr .r8, 8192⟩] s.mem s₂.mem := by
    rw [k₂.2.1]; exact scratchFrame o₁ (by decide)
  have hr₂ : ∀ d, d + 8 ≤ 32 → InRegions (s₂.rd ++ s₂.wr) (off (s₂.gpr .rdx) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .rdx, 32⟩, ?_, ?_⟩
    · rw [k₂.2.2.1, rd₁, hs.rd]; simp
    · rw [g₂ .rdx (by decide)]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (copyScalar_ok hp₂ hw₂ .rdx (by decide) hr₂ 64 (by decide))
    fun s₃ ⟨v₃, g₃, rd₃, wr₃, o₃⟩ => ?_
  have hp₃ : s₃.gpr .rdi = s.gpr .r8 := (g₃ _ (by decide)).trans hp₂
  have hw₃ : (⟨s.gpr .r8, 8192⟩ : Region) ∈ s₃.wr := wr₃ ▸ hw₂
  have fm₃ := fm₂.trans (scratchFrame o₃ (by decide))
  have rcx₃ : s₃.gpr .rcx = s.gpr .rcx := (g₃ _ (by decide)).trans (g₂ _ (by decide))
  have hr₃ : ∀ d, d + 8 ≤ 32 → InRegions (s₃.rd ++ s₃.wr) (off (s₃.gpr .rcx) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .rcx, 32⟩, ?_, ?_⟩
    · rw [rd₃, k₂.2.2.1, rd₁, hs.rd]; simp
    · rw [rcx₃]; exact Offset.contains_base _ hd (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (copyScalar_ok hp₃ hw₃ .rcx (by decide) hr₃ 96 (by decide))
    fun s₄ ⟨v₄, g₄, rd₄, wr₄, o₄⟩ => ?_
  have fm₄ := fm₃.trans (scratchFrame o₄ (by decide))
  have rsi₄ : s₄.gpr .rsi = s.gpr .rsi :=
    (g₄ _ (by decide)).trans ((g₃ _ (by decide)).trans (g₂ _ (by decide)))
  have hr₄ : ∀ d, d + 8 ≤ 32 → InRegions (s₄.rd ++ s₄.wr) (off (s₄.gpr .rsi) d) 8 := by
    intro d hd
    refine ⟨⟨s.gpr .rsi, 32⟩, ?_, ?_⟩
    · rw [rd₄, rd₃, k₂.2.2.1, rd₁, hs.rd]; simp
    · rw [rsi₄]; exact Offset.contains_base _ hd (by omega)
  refine WP.mono (loadWords_ok s₄ .rsi (by decide) hr₄) fun t ⟨vt, kt⟩ => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kt.1 _ (by decide), g₄ _ (by decide)]; exact hp₃
  · rw [kt.1 _ (by decide), g₄ _ (by decide), g₃ _ (by decide), out₂, g₁]
  · rw [kt.1 _ (by decide), g₄ _ (by decide), g₃ _ (by decide), g₂ _ (by decide)]
  · rw [vt, rsi₄, fe_frame fm₄ hs.r_sc]
  · rw [kt.2.1, o₄.fe (by decide) (by decide), v₃, g₂ _ (by decide), fe_frame fm₂ hs.k_sc]
  · rw [kt.2.1, v₄, rcx₃, fe_frame fm₃ hs.s_sc]
  · rw [kt.2.2.1, rd₄, rd₃, k₂.2.2.1, rd₁]
  · rw [kt.2.2.2, wr₄, wr₃, k₂.2.2.2, wr₁]
  · have sv₂ : Saved (s.gpr .r8) s.gpr s₂.mem := by rw [k₂.2.1]; exact sv₁
    rw [kt.2.1]; exact (sv₂.outside o₃ (by decide)).outside o₄ (by decide)
  · rw [kt.2.1]; exact fm₄

end VG.Proof.Ed25519.X86_64
