import VerifiedGarbage.Proof.TripleDes.X86.Head
import VerifiedGarbage.Proof.TripleDes.X86.FinalSave
import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Proof.Rc2.X86 (addr32)

structure RestoredTailPost (original origin : State) (x : BitVec 64) (s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (dataArg origin)) =
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp x)
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = origin.rd
  wr : s.wr = origin.wr
  sp : s.gpr .esp = origin.gpr .esp
  frame : Frame [⟨addr32 (dataArg origin), 8⟩, workRegion origin] origin.mem s.mem

theorem blockTailRestored_ok (original s : State) (x : BitVec 64) (hword : WordState x s)
    (hsaved : Saved original s) (hok : Ok sboxCfg s)
    (dataFit : (dataArg s).toNat + 8 ≤ 2 ^ 32)
    (harg : InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) 2) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion s))
    (hw : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (s.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4) :
    WP isa (.block (finalSave ++ blockRestore ++ restoredOutput)) s (RestoredTailPost original s x) := by
  rw [WP.block_append_iff, WP.block_append_iff]
  apply WP.mono (finalSave_ok s hok)
  intro s₁ h₁
  have saved₁ := hsaved.congr h₁.bp h₁.frame
  have reads₁ : ∀ i < 4, InRegions (s₁.rd ++ s₁.wr) (addr32 (s₁.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [h₁.rd, h₁.wr, h₁.bp]; exact hread
  apply WP.mono (blockRestore_ok original s₁ saved₁ (by rw [h₁.bp]; exact hok.fit) reads₁)
  intro s₂ h₂
  have sp₂ : s₂.gpr .esp = s.gpr .esp := h₂.sp.trans h₁.sp
  have ptr₂ : s₂.gpr .eax = s.gpr .ebp := h₂.ptr.trans h₁.bp
  have rd₂ : s₂.rd = s.rd := h₂.rd.trans h₁.rd
  have wr₂ : s₂.wr = s.wr := h₂.wr.trans h₁.wr
  have data₂ : dataArg s₂ = dataArg s := by
    unfold dataArg
    rw [sp₂, h₂.mem]
    exact h₁.frame.readW (r := ⟨wordAddr (s.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hargSep) (by decide)
  have input₂ : finalWord s₂ = Spec.TripleDes.permute Spec.TripleDes.fp x := by
    unfold finalWord
    rw [ptr₂, h₂.mem]
    change (s₁.mem.readW (wordAddr (s.gpr .ebp) 7) 32 ++
      s₁.mem.readW (wordAddr (s.gpr .ebp) 6) 32 : BitVec 64) =
        Spec.TripleDes.permute Spec.TripleDes.fp x
    rw [h₁.hi, h₁.lo, VG.Proof.TripleDes.halves_append, hword.left, hword.right,
      VG.Proof.TripleDes.halves_append]
  have reads₂ : ∀ k ∈ [24, 28], InRegions (s₂.rd ++ s₂.wr) (addr (s₂.gpr .eax) k) 4 := by
    intro k hk
    rw [rd₂, wr₂, ptr₂]
    have hwk : InRegions s.wr (addr (s.gpr .ebp) k) 4 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl
      · exact hok.slotIn 6 (by decide)
      · exact hok.slotIn 7 (by decide)
    obtain ⟨r, hr, hc⟩ := hwk
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [rd₂, wr₂, sp₂]; exact harg
  have writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (dataArg s₂) i) 4 := by
    rw [wr₂, data₂]; exact hw
  obtain ⟨s₃, run₃, mem₃, rd₃, wr₃, regs₃⟩ := restoredOutput_ok s₂
    (by rw [data₂]; exact dataFit) arg₂ reads₂ writes₂
  have hm : s₃.mem = s₁.mem.writeW (addr32 (dataArg s))
      (byteRev64 (Spec.TripleDes.permute Spec.TripleDes.fp x)) := by
    rw [mem₃, data₂, input₂, h₂.mem]
  refine WP.of_runBlock ⟨s₃, run₃, ⟨?_, ?_, rd₃.trans rd₂, wr₃.trans wr₂,
    (regs₃ .esp (by decide) (by decide) (by decide)).trans sp₂, ?_⟩⟩
  · rw [hm]
    exact blockAt_writeW _ _ _
  · intro r hr
    have neq : ∀ r ∈ savedRegs, r ≠ .eax ∧ r ≠ .ecx ∧ r ≠ .edx := by decide
    exact (regs₃ r (neq r hr).1 (neq r hr).2.1 (neq r hr).2.2).trans (h₂.saved r hr)
  · rw [hm]
    exact (h₁.frame.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).writeW
      (List.mem_cons_self) _ (Region.contains_self _ _)

end VG.Proof.TripleDes.X86
