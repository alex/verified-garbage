import VerifiedGarbage.Proof.TripleDes.X86.Body
import VerifiedGarbage.Proof.TripleDes.X86.Initial
import VerifiedGarbage.Proof.TripleDes.X86.Save

namespace VG.Proof.TripleDes.X86
open VG VG.X86 VG.X86.RegUpd VG.X86.Straight VG.Impl.TripleDes.X86
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.Rc2.X86 (addr32)

def prepared (s : State) : State := s.setReg .ebp (scratchArg s 3)
def saveRegion (s : State) : Region := ⟨addr32 (scratchArg s 3), 16⟩

structure HeadPre (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  ready : Ready keys base (prepared s)
  scratchFit : (scratchArg s 3).toNat + 512 ≤ 2 ^ 32
  dataFit : (dataArg s).toNat + 8 ≤ 2 ^ 32
  saveWrite : ∀ i < 4, InRegions s.wr (addr32 (scratchArg s 3) + BitVec.ofNat 64 (4 * i)) 4
  argRead : ∀ i ∈ [1, 2, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4
  argSeparate : ∀ i ∈ [1, 2, 3], (⟨wordAddr (s.gpr .esp) i, 4⟩ : Region).Disjoint (saveRegion s)
  dataRead : ∀ i < 2, InRegions (s.rd ++ s.wr) (wordAddr (dataArg s) i) 4
  dataSeparate : (⟨addr32 (dataArg s), 8⟩ : Region).Disjoint (saveRegion s)
  keySeparate : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (saveRegion s)

structure HeadPost (keys : Nat → DesSchedule) (base : BitVec 32) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (addr32 (dataArg original))))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  bp : s.gpr .ebp = scratchArg original 3
  sp : s.gpr .esp = original.gpr .esp
  data : dataArg s = dataArg original
  frame : Frame [saveRegion original] original.mem s.mem

theorem blockHead_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State)
    (hp : HeadPre keys base s) : WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  rw [WP.block_append_iff, blockSave]
  apply WP.mono (saveWithArg_ok s 3 (hp.argRead 3 (by decide)) hp.scratchFit hp.saveWrite)
  intro s₁ h₁
  have sp₁ : s₁.gpr .esp = s.gpr .esp := h₁.reg .esp (by decide) (by decide)
  have frame₁ : Frame [saveRegion s] s.mem s₁.mem := h₁.frame
  have bp₁ : s₁.gpr .ebp = (prepared s).gpr .ebp := h₁.bp
  have sp₁' : s₁.gpr .esp = (prepared s).gpr .esp := by
    rw [prepared, gpr_setReg_of_ne _ _ (by decide)]; exact sp₁
  have ready₁ : Ready keys base s₁ := hp.ready.congrFrame bp₁ sp₁' h₁.rd h₁.wr
    [saveRegion s] frame₁
    (by intro q hq; obtain rfl := List.mem_singleton.mp hq
        rw [prepared, gpr_setReg_of_ne _ _ (by decide)]
        exact hp.argSeparate 1 (by decide))
    (by intro c hc d j hj i hi q hq; obtain rfl := List.mem_singleton.mp hq
        exact hp.keySeparate c hc d j hj i hi)
  have data₁ : dataArg s₁ = dataArg s := by
    unfold dataArg
    rw [sp₁]
    exact frame₁.readW (r := ⟨wordAddr (s.gpr .esp) 2, 4⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.argSeparate 2 (by decide)) (by decide)
  have args₁ : InRegions (s₁.rd ++ s₁.wr) (wordAddr (s₁.gpr .esp) 2) 4 := by
    rw [sp₁, h₁.rd, h₁.wr]; exact hp.argRead 2 (by decide)
  have reads₁ : ∀ i < 2, InRegions (s₁.rd ++ s₁.wr) (wordAddr (dataArg s₁) i) 4 := by
    rw [h₁.rd, h₁.wr, data₁]; exact hp.dataRead
  have input₁ : Spec.TripleDes.blockAt s₁.mem (addr32 (dataArg s₁)) =
      Spec.TripleDes.blockAt s.mem (addr32 (dataArg s)) := by
    rw [data₁]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ frame₁
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  apply WP.mono (blockLoad_ok s₁ (by rw [data₁]; exact hp.dataFit) args₁ reads₁)
  intro s₂ h₂
  have hf : Frame [workRegion s₁] s₁.mem s₂.mem := by rw [h₂.mem]; exact Frame.refl _ _
  have input := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) input₁
  refine ⟨⟨h₂.l.trans (congrArg (fun x : BitVec 64 => (x >>> 32).setWidth 32) input),
    h₂.r.trans (congrArg (fun x : BitVec 64 => x.setWidth 32) input)⟩,
    ready₁.congr h₂.bp h₂.sp h₂.rd h₂.wr hf, h₁.saved.congr h₂.bp hf,
    h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.bp.trans h₁.bp, h₂.sp.trans sp₁, ?_, ?_⟩
  · unfold dataArg
    rw [h₂.mem, h₂.sp]
    exact data₁
  · rw [h₂.mem]; exact frame₁

end VG.Proof.TripleDes.X86
