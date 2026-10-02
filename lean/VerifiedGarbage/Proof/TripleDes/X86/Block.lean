import VerifiedGarbage.Proof.TripleDes.X86.Head
import VerifiedGarbage.Proof.TripleDes.X86.RestoredTail

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction Schedule)
open VG.Proof.Rc2.X86 (addr32)

def blockResult (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) : Spec.TripleDes.Block :=
  match d with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (d : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) d
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) = blockResult keys d b := by
  cases d
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region :=
  [⟨addr32 (dataArg s), 8⟩, ⟨addr32 (scratchArg s 3), 512⟩]

structure BlockPost (keys : Schedule) (d : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (addr32 (dataArg original)) =
    blockResult keys d (Spec.TripleDes.blockAt original.mem (addr32 (dataArg original)))
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.gpr .esp = original.gpr .esp
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (d : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hread : ∀ i < 4, InRegions (s.rd ++ s.wr) (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4)
    (hwrite : ∀ i < 2, InRegions s.wr (wordAddr (dataArg s) i) 4)
    (hargSep : (⟨wordAddr (s.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion (prepared s))) :
    WP isa (block d) s (BlockPost keys d s) := by
  rw [block]
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ h₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ d h₁.ready h₁.word)
  intro s₂ h₂
  have stable := h₂.2.2
  have bp₂ : s₂.gpr .ebp = scratchArg s 3 := stable.bp.trans h₁.bp
  have sp₂ : s₂.gpr .esp = s.gpr .esp := stable.sp.trans h₁.sp
  have work₁ : workRegion s₁ = workRegion (prepared s) := by
    unfold workRegion prepared
    rw [h₁.bp, VG.X86.RegUpd.gpr_setReg_self]
  have data₂ : dataArg s₂ = dataArg s := by
    unfold dataArg
    rw [stable.sp]
    have sep : (⟨wordAddr (s₁.gpr .esp) 2, 4⟩ : Region).Disjoint (workRegion s₁) := by
      rw [h₁.sp, work₁]
      exact hargSep
    have hm := stable.frame.readW (a := wordAddr (s₁.gpr .esp) 2) (w := 32)
      (r := ⟨wordAddr (s₁.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact sep) (by decide)
    exact hm.trans h₁.data
  have saved₂ := h₁.saved.congr stable.bp stable.frame
  have reads₂ : ∀ i < 4, InRegions (s₂.rd ++ s₂.wr) (addr32 (s₂.gpr .ebp) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, bp₂]; exact hread
  have writes₂ : ∀ i < 2, InRegions s₂.wr (wordAddr (dataArg s₂) i) 4 := by
    rw [stable.wr, h₁.wr, data₂]; exact hwrite
  have arg₂ : InRegions (s₂.rd ++ s₂.wr) (wordAddr (s₂.gpr .esp) 2) 4 := by
    rw [stable.rd, stable.wr, h₁.rd, h₁.wr, sp₂]; exact hp.argRead 2 (by decide)
  have work₂ : workRegion s₂ = workRegion (prepared s) := by
    unfold workRegion prepared
    rw [bp₂, VG.X86.RegUpd.gpr_setReg_self]
  apply WP.mono (blockTailRestored_ok s s₂ _ h₂.1 saved₂ h₂.2.1.spills
    (by rw [data₂]; exact hp.dataFit) arg₂
    (by rw [sp₂, work₂]; exact hargSep) writes₂ reads₂)
  intro s₃ h₃
  refine ⟨?_, h₃.saved, h₃.rd.trans (stable.rd.trans h₁.rd), h₃.wr.trans (stable.wr.trans h₁.wr),
    h₃.sp.trans sp₂, ?_⟩
  · have hr := h₃.result
    rw [data₂] at hr
    exact hr.trans (blockResult_core keys d _)
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := h₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := stable.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], ?_⟩
      unfold workRegion
      rw [h₁.bp]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := h₃.frame.sub (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [data₂]
        exact ⟨⟨addr32 (dataArg s), 8⟩, by simp [blockRegions], fun _ h => h⟩
      · refine ⟨⟨addr32 (scratchArg s 3), 512⟩, by simp [blockRegions], ?_⟩
        unfold workRegion
        rw [bp₂]
        exact Offset.sub_base _ (by decide))
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.X86
