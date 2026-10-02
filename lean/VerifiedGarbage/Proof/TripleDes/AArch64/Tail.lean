import VerifiedGarbage.Proof.TripleDes.AArch64.Store
import VerifiedGarbage.Proof.TripleDes.AArch64.Save
import VerifiedGarbage.Proof.TripleDes.AArch64.WordState

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.Impl.TripleDes.AArch64

structure TailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (origin.gpr .x1) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.sp = origin.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = origin.gpr q
  frame : Frame [⟨origin.gpr .x1, 8⟩] origin.mem s.mem

theorem blockTail_ok (original s : State) (x : BitVec 64)
    (hword : WordState x s) (hsaved : Saved original s)
    (hsavedRead : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8)
    (hwrite : InRegions s.wr (s.gpr .x1) 8) :
    WP isa (.block (blockStore ++ blockRestore ++ ([.str .x .x3 .x1 0] : List Instr)))
      s (TailPost original s x) := by
  obtain ⟨s₁, run₁, word₁, mem₁, rd₁, wr₁, sp₁, regs₁⟩ :=
    blockStore_ok s ((x >>> 32).setWidth 32) (x.setWidth 32) hword.left hword.right
  have word : s₁.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    word₁.trans (congrArg (fun v => rev64 (Spec.TripleDes.permute Spec.TripleDes.fp v))
      (VG.Proof.TripleDes.halves_append x))
  have saved₁ : Saved original s₁ := by
    intro i hi
    rw [regs₁ .x2 (by decide), mem₁]
    exact hsaved i hi
  have savedRead₁ : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8 := by
    rw [rd₁, wr₁, regs₁ .x2 (by decide)]
    exact hsavedRead
  apply WP.block_append
  apply WP.block_append
  apply WP.of_runBlock
  refine ⟨s₁, run₁, ?_⟩
  apply WP.mono (blockRestore_ok original s₁ saved₁ savedRead₁)
  intro s₂ hs₂
  have hnonsaved : ∀ q ∈ (.x3 :: roundStepKept), q ∉ savedRegs := by decide
  have hrax₂ : s₂.gpr .x3 = rev64 (Spec.TripleDes.permute Spec.TripleDes.fp x) :=
    (hs₂.keep.reg .x3 (hnonsaved .x3 (by decide))).trans word
  have hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ (.x3 :: roundStepKept) ∧
      r ∈ loadKept := by decide
    exact (hs₂.keep.reg q (hnonsaved q (hkeep q hq).1)).trans (regs₁ q (hkeep q hq).2)
  have hwrite₂ : InRegions s₂.wr (s₂.gpr .x1) 8 := by
    rw [hs₂.keep.wr, wr₁, hregs₂ .x1 (by decide)]
    exact hwrite
  obtain ⟨s₃, run₃, mem₃, gpr₃, rd₃, wr₃, sp₃⟩ := writeData_ok s₂ hwrite₂
  apply WP.of_runBlock
  refine ⟨s₃, run₃, ?_, ?_, rd₃.trans (hs₂.keep.rd.trans rd₁),
    wr₃.trans (hs₂.keep.wr.trans wr₁), sp₃.trans (hs₂.sp.trans sp₁), ?_, ?_⟩
  · rw [mem₃, hs₂.keep.mem, mem₁, hregs₂ .x1 (by decide), hrax₂]
    exact blockAt_writeW s.mem (s.gpr .x1) (Spec.TripleDes.permute Spec.TripleDes.fp x)
  · intro r hr
    rw [gpr₃]
    exact hs₂.saved r hr
  · intro q hq
    rw [gpr₃]
    exact hregs₂ q hq
  · rw [mem₃, hs₂.keep.mem, mem₁, hregs₂ .x1 (by decide)]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.TripleDes.AArch64
