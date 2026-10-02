import VerifiedGarbage.Proof.TripleDes.X86_64.Body
import VerifiedGarbage.Proof.TripleDes.X86_64.BlockIO
import VerifiedGarbage.Proof.TripleDes.X86_64.Save

namespace VG.Proof.TripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Impl.TripleDes.X86_64
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨s.gpr .rdx, 56⟩

structure HeadPre (keys : Nat → DesSchedule) (base : Addr) (s : State) : Prop where
  spills : Ok sboxCfg s
  pointer : s.gpr .rdi = base
  saveRead : ∀ i < 7, InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8
  saveWrite : ∀ i < 7, InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 (8 * i)) 8
  countRead : InRegions (s.rd ++ s.wr) (countAddr s) 8
  countWrite : InRegions s.wr (countAddr s) 8
  dataRead : InRegions (s.rd ++ s.wr) (s.gpr .rsi) 8
  dataSeparate : (⟨s.gpr .rsi, 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    InRegions (s.rd ++ s.wr) (keyAddr (componentBase base c) d j) 8
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (workRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (⟨keyAddr (componentBase base c) d j, 8⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (s.mem.readW (keyAddr (componentBase base c) d j) 64).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : Addr) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (original.gpr .rsi)))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  regs : ∀ q ∈ [Reg.rdi, .rsi, .rdx, .rsp], s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : Addr} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hsaved : Saved s t) (hf : Frame [saveRegion s] s.mem t.mem) :
    Ready keys base t := by
  have hbase : t.gpr .rdx = s.gpr .rdx := congrFun hg .rdx
  refine ⟨hp.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hsaved 6 (by decide)).trans hp.pointer
  · rw [hrd, hwr, show savedKeyAddr t = savedKeyAddr s from congrArg (· + BitVec.ofNat 64 48) hbase]
    exact hp.saveRead 6 (by decide)
  · rw [hrd, hwr, show countAddr t = countAddr s from congrArg (· + BitVec.ofNat 64 56) hbase]
    exact hp.countRead
  · rw [hwr, show countAddr t = countAddr s from congrArg (· + BitVec.ofNat 64 56) hbase]
    exact hp.countWrite
  · rw [hrd, hwr]; exact hp.read
  · rw [show workRegion t = workRegion s from
      congrArg (fun p => (⟨p + BitVec.ofNat 64 56, 392⟩ : Region)) hbase]
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
  have hready := ready_afterSave hp hs₁.1 hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2.1 hs₁.2.2.2.2
  have hread₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rsi) 8 := by
    rw [hs₁.2.1, hs₁.2.2.1, hs₁.1]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (s₁.gpr .rsi) =
      Spec.TripleDes.blockAt s.mem (s.gpr .rsi) := by
    rw [hs₁.1]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.2.2.2.2
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, regs₂⟩ := blockLoad_ok s₁ hread₁
  have hframe : Frame [workRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .rdx (by decide)) rd₂ wr₂ hframe,
    hs₁.2.2.2.1.congr (regs₂ .rdx (by decide)) hframe,
    rd₂.trans hs₁.2.1, wr₂.trans hs₁.2.2.1, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => ((x >>> 32).setWidth 32).setWidth 64) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => (x.setWidth 32).setWidth 64) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.1 q)
  · rw [mem₂]; exact hs₁.2.2.2.2

end VG.Proof.TripleDes.X86_64
