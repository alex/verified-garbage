import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Ed25519.AArch64.MulAdd
import VerifiedGarbage.Proof.Ed25519.AArch64.MulAddCodec
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarMain
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract

/-! Merged from `Proof.Ed25519.AArch64.MulAddLit`. -/
section
/-! The kernel checks this literal once; taint and instruction checks reuse it. -/
namespace VG
materialize_code Impl.Ed25519.AArch64.scalarMulAdd
end VG
end

/-! Merged from `Proof.Ed25519.AArch64.MulAddMain`. -/
section
/-! Merged from `Proof.Ed25519.AArch64.MulAddSetup`. -/
section
/-! Save the caller's registers and prepare the scalar operands. -/

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
end

/-! Full-width multiply-add followed by subgroup reduction. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64
open VG.Spec.Ed25519 (bytesAt decodeLE)

def scalarMulAddLocal : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x1, 32⟩, ⟨s.gpr .x2, 32⟩, ⟨s.gpr .x3, 32⟩] ∧
    s.wr = [⟨s.gpr .x0, 32⟩, ⟨s.gpr .x4, 8192⟩] ∧
    (⟨s.gpr .x1, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x2, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (⟨s.gpr .x3, 32⟩ : Region).Disjoint ⟨s.gpr .x4, 8192⟩ ∧
    (s.gpr .x4).toNat + 8192 ≤ 2 ^ 64
  post s t := bytesAt t.mem (s.gpr .x0) 32 = Spec.Ed25519.scalarMulAdd
    (bytesAt s.mem (s.gpr .x1) 32) (bytesAt s.mem (s.gpr .x2) 32) (bytesAt s.mem (s.gpr .x3) 32)
  pub s t := s.sp = t.sp ∧ s.gpr .x0 = t.gpr .x0 ∧
    s.gpr .x1 = t.gpr .x1 ∧ s.gpr .x2 = t.gpr .x2 ∧
    s.gpr .x3 = t.gpr .x3 ∧ s.gpr .x4 = t.gpr .x4

theorem MulAddPre.of {s : State} (h : scalarMulAddLocal.pre s) : MulAddPre s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem scalarMulAdd_correct {s : State} (hs : MulAddPre s) :
    WP isa scalarMulAdd s fun t => abiPreserved s t ∧ scalarMulAddLocal.post s t := by
  apply WP.withPreservedV (hc := by lit_decide)
  have hw : (⟨s.gpr .x4, 8192⟩ : Region) ∈ s.wr := by rw [hs.wr]; simp
  rw [scalarMulAdd]
  refine WP.seq (WP.mono (mulAddSetup_ok hs) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (wideAccumulate_ok ⟨h₁.base, h₁.wr ▸ hw, hs.nowrap⟩
    (by constructor <;> decide) (by constructor <;> decide)) fun s₂ ⟨v₂, k₂⟩ => ?_)
  have prod₂ : wideValue s₂ = fe s.mem (s.gpr .x1) 0 +
      fe s.mem (s.gpr .x2) 0 * fe s.mem (s.gpr .x3) 0 := by
    rw [v₂, h₁.value, h₁.left, h₁.right]
  have base₂ : s₂.gpr .x0 = s.gpr .x4 := (k₂.gpr _ (by decide)).trans h₁.base
  have wr₂ : s₂.wr = s.wr := k₂.wr.trans h₁.wr
  apply WP.seq
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (storeWide_ok ⟨base₂, wr₂ ▸ hw, hs.nowrap⟩) fun s₃ ⟨v₃, g₃, rd₃, wr₃, sp₃, o₃⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceArgs_ok s₃) fun s₄ ⟨x1₄, x2₄, x0₄, k₄⟩ => ?_
  refine WP.mono (scalarInit_ok s₄) fun s₅ ⟨b₅, v₅, z₅, k₅⟩ => ?_
  have x1₅ : s₅.gpr .x1 = off (s.gpr .x4) 128 := by rw [k₅.gpr _ (by decide), x1₄, g₃, base₂]
  have x2₅ : s₅.gpr .x2 = s.gpr .x4 := by rw [k₅.gpr _ (by decide), x2₄, g₃, base₂]
  have x0₅ : s₅.gpr .x0 = s.gpr .x0 := by
    rw [k₅.gpr _ (by decide), x0₄, g₃, k₂.gpr _ (by decide), h₁.out]
  have wr₅ : s₅.wr = s.wr := by rw [k₅.wr, k₄.wr, wr₃, wr₂]
  have read₅ : ∀ k < 8,
      InRegions (s₅.rd ++ s₅.wr) (s₅.gpr .x1 + BitVec.ofNat 64 (8 * k)) 8 := by
    intro k hk
    refine ⟨⟨s.gpr .x4, 8192⟩, List.mem_append_right _ (wr₅ ▸ hw), ?_⟩
    rw [x1₅, Offset.add_add]; exact Offset.contains_base _ (by omega) (by omega)
  have sv₅ : Saved (s.gpr .x4) s.gpr s₅.mem := by
    have sv₂ : Saved (s.gpr .x4) s.gpr s₂.mem := by rw [k₂.mem]; exact h₁.saved
    rw [k₅.mem, k₄.mem]; exact sv₂.outside o₃ (by decide)
  apply WP.seq
  refine WP.mono (scalarLoop_ok s₅ b₅ v₅ read₅ z₅) fun s₆ ⟨v₆, k₆⟩ => ?_
  have wr₆ : s₆.wr = s.wr := k₆.wr.trans wr₅
  have val₆ : scalarValue s₆ = (fe s.mem (s.gpr .x1) 0 +
      fe s.mem (s.gpr .x2) 0 * fe s.mem (s.gpr .x3) 0) % Spec.Ed25519.L := by
    rw [v₆, x1₅, k₅.mem, k₄.mem, v₃, prod₂]
  rw [scalarFinish, WP.block_append_iff]
  refine WP.mono (scalarRestore_ok (g := s.gpr) ((k₆.gpr _ (by decide)).trans x2₅) (wr₆ ▸ hw)
    (by rw [k₆.mem]; exact sv₅)) fun s₇ ⟨rest₇, k₇⟩ => ?_
  have x0₇ : s₇.gpr .x0 = s.gpr .x0 :=
    (k₇.gpr _ (by decide)).trans ((k₆.gpr _ (by decide)).trans x0₅)
  have hwo : (⟨s.gpr .x0, 32⟩ : Region) ∈ s₇.wr := by rw [k₇.wr, wr₆, hs.wr]; simp
  refine WP.mono (scalarOut_ok x0₇ hwo) fun t ht => ?_
  subst t
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rest₇ (.x19, 0) (by decide)
    · exact rest₇ (.x20, 8) (by decide)
    · exact rest₇ (.x21, 16) (by decide)
    · exact rest₇ (.x22, 24) (by decide)
    · exact rest₇ (.x23, 32) (by decide)
    · exact rest₇ (.x24, 40) (by decide)
    all_goals
      rw [k₇.gpr _ (by decide), k₆.gpr _ (by decide), k₅.gpr _ (by decide),
        k₄.gpr _ (by decide), g₃, k₂.gpr _ (by decide), h₁.preserved _ (by decide)]
  · exact k₇.sp.trans (k₆.sp.trans (k₅.sp.trans (k₄.sp.trans (sp₃.trans (k₂.sp.trans h₁.sp)))))
  · change Spec.X25519.bytesAt (st4 _ _ _ _ _ _ _) _ 32 = _
    rw [bytesAt_st4, Spec.Ed25519.scalarMulAdd, encodeLE_eq]
    apply congrArg (Proof.X25519.leBytes 32)
    have v₇ : scalarValue s₇ = scalarValue s₆ := by
      simp only [scalarValue, k₇.gpr .x4 (by decide), k₇.gpr .x5 (by decide), k₇.gpr .x6 (by decide),
        k₇.gpr .x7 (by decide)]
    change scalarValue s₇ = _
    rw [v₇, val₆]
    have hd (p : Addr) : decodeLE (bytesAt s.mem p 32) = fe s.mem p 0 := by
      have h := decodeLE_words s.mem p 0
      rw [show off p 0 = p from BitVec.add_zero p] at h
      exact h
    rw [hd, hd, hd]

end VG.Proof.Ed25519.AArch64
end

/-! Scalar multiply-add satisfies the merged specification, ABI, and constant-time contract. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def mulAddSatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | .x4 => 0x5000 | _ => 0
  sp := 0x9000
  mem _ := 0
  rd := [⟨0x2000, 32⟩, ⟨0x3000, 32⟩, ⟨0x4000, 32⟩]
  wr := [⟨0x1000, 32⟩, ⟨0x5000, 8192⟩]

theorem scalarMulAdd_ok (s : State) (hs : scalarMulAddLocal.pre s) :
    ∃ t s', Exec isa scalarMulAdd s t s' ∧ abiPreserved s s' ∧ scalarMulAddLocal.post s s' :=
  scalarMulAdd_correct (MulAddPre.of hs)

theorem scalarMulAdd_ct : ConstantTime isa scalarMulAddLocal.pre scalarMulAddLocal.pub scalarMulAdd := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨hsp, h0, h1, h2, h3, h4⟩
  refine ⟨hsp, fun r hr => ?_⟩
  simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption

theorem scalarMulAdd_verified : Verified AArch64.target scalarMulAdd
    (Spec.Ed25519.scalarMulAddContract AArch64.abi) :=
  Verified.of_correct scalarMulAdd_ok scalarMulAdd_ct (by
    sig_implies [Spec.Ed25519.scalarMulAddContract, Spec.Ed25519.scalarMulAddSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, scalarMulAddLocal]
      [mulAddSatState] using mulAddSatState)

end VG.Proof.Ed25519.AArch64
