import VerifiedGarbage.Proof.TripleDes.AArch64.Body
import VerifiedGarbage.Proof.TripleDes.AArch64.BlockIO
import VerifiedGarbage.Proof.TripleDes.AArch64.Save

namespace VG.Proof.TripleDes.AArch64

open VG VG.AArch64 VG.AArch64.Straight VG.Impl.TripleDes.AArch64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨s.gpr .x2, 32⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  pointer : s.gpr .x0 = base
  saveRead : ∀ i < 4, InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 4, InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 (8 * i)) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8
  dataSeparate : (⟨s.gpr .x1, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .x1)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  have hbase : t.gpr .x2 = s.gpr .x2 := congrFun hg .x2
  refine ⟨hp.spills.congr hbase hbase hrd hwr, (congrFun hg .x0).trans hp.pointer, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 32, 384⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    have hmem := hf.readW (a := keyAddr (componentBase base c) d j) (w := 64)
      (r := ⟨keyAddr (componentBase base c) d j, 8⟩) (Region.contains_self _ _)
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj)
      (by decide)
    exact (congrArg (BitVec.setWidth 48) hmem).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : Addr) (s : State)
    (hp : HeadPre keys base s) :
    WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (blockSave_ok s hp.saveWrite)
  intro s₁ hs₁
  have hready := ready_afterSave hp hs₁.gpr hs₁.rd hs₁.wr hs₁.frame
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x1) 8 := by
    rw [hs₁.rd, hs₁.wr, hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (s₁.gpr .x1) =
      Spec.TripleDes.blockAt s.mem (s.gpr .x1) := by
    rw [hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.frame
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, sp₂, regs₂⟩ := blockLoad_ok s₁ hread₁
  have hframe : Frame [spillRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .x2 (by decide)) (regs₂ .x0 (by decide)) rd₂ wr₂ hframe,
    hs₁.saved.congr (regs₂ .x2 (by decide)) hframe,
    rd₂.trans hs₁.rd, wr₂.trans hs₁.wr, sp₂.trans hs₁.sp, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.gpr q)
  · rw [mem₂]; exact hs₁.frame

end VG.Proof.TripleDes.AArch64
