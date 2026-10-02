import VerifiedGarbage.Proof.TripleDes.Arm.Body
import VerifiedGarbage.Proof.TripleDes.Arm.BlockIO
import VerifiedGarbage.Proof.TripleDes.Arm.Save

namespace VG.Proof.TripleDes.Arm
open VG VG.Arm VG.Arm.Straight VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction DesSchedule)
open VG.Proof.TripleDes (roundKey)

def saveRegion (s : State) : Region := ⟨State.addr (s.gpr .r2), 36⟩

structure HeadPre (keys : Nat → DesSchedule) (base : BitVec 32) (s : State) : Prop where
  spills : Ok sboxCfg s
  scratchFit : (s.gpr .r2).toNat + 256 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 ≤ 2 ^ 32
  pointer : s.gpr .r0 = base
  saveRead : ∀ i < 9, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  saveWrite : ∀ i < 9, InRegions s.wr (State.addr (s.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4
  dataRead : ∀ t < 2, InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4
  dataSeparate : (⟨State.addr (s.gpr .r1), 8⟩ : Region).Disjoint (saveRegion s)
  read : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    InRegions (s.rd ++ s.wr) (wordAddr (keyAddr (componentBase base c) d j) t) 4
  separateWork : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (spillRegion s)
  separateSave : ∀ c < 3, ∀ d : Direction, ∀ j < 16, ∀ t < 2,
    (⟨wordAddr (keyAddr (componentBase base c) d j) t, 4⟩ : Region).Disjoint (saveRegion s)
  values : ∀ c < 3, ∀ d : Direction, ∀ j < 16,
    (readKey s.mem (keyAddr (componentBase base c) d j)).setWidth 48 = roundKey (keys c) d j

structure HeadPost (keys : Nat → DesSchedule) (base : BitVec 32) (original s : State) : Prop where
  word : WordState (Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1))))) s
  ready : Ready keys base s
  saved : Saved original s
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ loadKept, s.gpr q = original.gpr q
  frame : Frame [saveRegion original] original.mem s.mem

theorem ready_afterSave {keys : Nat → DesSchedule} {base : BitVec 32} {s t : State}
    (hp : HeadPre keys base s) (hg : t.gpr = s.gpr) (hrd : t.rd = s.rd)
    (hwr : t.wr = s.wr) (hf : Frame [saveRegion s] s.mem t.mem) : Ready keys base t := by
  have hbase : t.gpr .r2 = s.gpr .r2 := congrFun hg .r2
  refine ⟨hp.spills.congr hbase hbase hrd hwr, ?_, ?_, ?_⟩
  · rw [hrd, hwr]; exact hp.read
  · rw [show spillRegion t = spillRegion s from
      congrArg (fun p => (⟨State.addr p + BitVec.ofNat 64 60, 388⟩ : Region)) hbase]
    exact hp.separateWork
  · intro c hc d j hj
    have hm := readKey_frame hf (ptr := keyAddr (componentBase base c) d j)
      (fun t ht q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.separateSave c hc d j hj t ht)
    exact (congrArg (BitVec.setWidth 48) hm).trans (hp.values c hc d j hj)

theorem blockHead_ok (keys : Nat → DesSchedule) (base : BitVec 32) (s : State)
    (hp : HeadPre keys base s) : WP isa (.block (blockSave ++ blockLoad)) s (HeadPost keys base s) := by
  apply WP.block_append
  apply WP.mono (blockSave_ok s hp.scratchFit hp.saveWrite)
  intro s₁ hs₁
  have hready := ready_afterSave hp hs₁.gpr hs₁.rd hs₁.wr hs₁.frame
  have hread₁ : ∀ t < 2, InRegions (s₁.rd ++ s₁.wr)
      (State.addr (s₁.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₁.rd, hs₁.wr, hs₁.gpr]; exact hp.dataRead
  have hdata : Spec.TripleDes.blockAt s₁.mem (State.addr (s₁.gpr .r1)) =
      Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r1)) := by
    rw [hs₁.gpr]
    exact VG.Proof.TripleDes.blockAt_eq_of_frame _ hs₁.frame
      (fun q hq => by obtain rfl := List.mem_singleton.mp hq; exact hp.dataSeparate)
  obtain ⟨s₂, run₂, left₂, right₂, mem₂, rd₂, wr₂, sp₂, regs₂⟩ :=
    blockLoad_ok s₁ (by rw [hs₁.gpr]; exact hp.dataFit) hread₁
  have hframe : Frame [spillRegion s₁] s₁.mem s₂.mem := by
    rw [mem₂]; exact Frame.refl _ _
  have hinput := congrArg (fun b => Spec.TripleDes.permute Spec.TripleDes.ip
    (Spec.TripleDes.decodeBlock b)) hdata
  apply WP.of_runBlock
  refine ⟨s₂, run₂, ?_, hready.congr (regs₂ .r2 (by decide)) rd₂ wr₂ hframe,
    hs₁.saved.congr (regs₂ .r2 (by decide)) hframe,
    rd₂.trans hs₁.rd, wr₂.trans hs₁.wr, sp₂.trans hs₁.sp, ?_, ?_⟩
  · exact ⟨left₂.trans (congrArg (fun x : BitVec 64 => (x >>> 32).setWidth 32) hinput),
      right₂.trans (congrArg (fun x : BitVec 64 => x.setWidth 32) hinput)⟩
  · intro q hq
    exact (regs₂ q hq).trans (congrFun hs₁.gpr q)
  · rw [mem₂]; exact hs₁.frame

end VG.Proof.TripleDes.Arm
