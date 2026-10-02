import VerifiedGarbage.Proof.TripleDes.Arm.Head
import VerifiedGarbage.Proof.TripleDes.Arm.Tail

namespace VG.Proof.TripleDes.Arm

open VG VG.Arm VG.Impl.TripleDes.Arm
open VG.Spec.TripleDes (Direction Schedule)

def blockResult (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.Block :=
  match direction with
  | .encrypt => Spec.TripleDes.encryptBlock keys b
  | .decrypt => Spec.TripleDes.decryptBlock keys b

theorem blockResult_core (keys : Schedule) (direction : Direction) (b : Spec.TripleDes.Block) :
    Spec.TripleDes.encodeBlock (Spec.TripleDes.permute Spec.TripleDes.fp
      (blockCore (Spec.TripleDes.componentSchedule keys) direction
        (Spec.TripleDes.permute Spec.TripleDes.ip (Spec.TripleDes.decodeBlock b)))) =
      blockResult keys direction b := by
  cases direction
  · exact (VG.Proof.TripleDes.encryptBlock_eq_cores keys b).symm
  · exact (VG.Proof.TripleDes.decryptBlock_eq_cores keys b).symm

def blockRegions (s : State) : List Region := [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩]

structure BlockPost (keys : Schedule) (direction : Direction) (original s : State) : Prop where
  result : Spec.TripleDes.blockAt s.mem (State.addr (original.gpr .r1)) =
    blockResult keys direction (Spec.TripleDes.blockAt original.mem (State.addr (original.gpr .r1)))
  pointer : s.gpr .r0 = original.gpr .r0
  saved : ∀ r ∈ savedRegs, s.gpr r = original.gpr r
  rd : s.rd = original.rd
  wr : s.wr = original.wr
  sp : s.sp = original.sp
  regs : ∀ q ∈ roundStepKept, s.gpr q = original.gpr q
  frame : Frame (blockRegions original) original.mem s.mem

theorem block_ok (keys : Schedule) (base : BitVec 32) (direction : Direction) (s : State)
    (hp : HeadPre (Spec.TripleDes.componentSchedule keys) base s)
    (hwrite : ∀ t < 2, InRegions s.wr (State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (block direction) s (BlockPost keys direction s) := by
  apply WP.seq
  apply WP.mono (blockHead_ok (Spec.TripleDes.componentSchedule keys) base s hp)
  intro s₁ hs₁
  apply WP.seq
  apply WP.mono (blockBody_ok (Spec.TripleDes.componentSchedule keys) base s₁ _ direction ((hs₁.regs .r0 (by decide)).trans hp.pointer) hs₁.ready hs₁.word)
  intro s₂ hs₂
  have hregs₂ : ∀ q ∈ roundStepKept, s₂.gpr q = s.gpr q := by
    intro q hq
    have hkeep : ∀ r ∈ roundStepKept, r ∈ loadKept := by decide
    exact (hs₂.2.2.1.regs q hq).trans (hs₁.regs q (hkeep q hq))
  have saved₂ := hs₁.saved.congr (hs₂.2.2.1.regs .r2 (by decide)) hs₂.2.2.1.frame
  have savedRead₂ : ∀ i < 9, InRegions (s₂.rd ++ s₂.wr) (State.addr (s₂.gpr .r2) + BitVec.ofNat 64 (4 * i)) 4 := by
    rw [hs₂.2.2.1.rd, hs₂.2.2.1.wr, hs₁.rd, hs₁.wr, hregs₂ .r2 (by decide)]
    exact hp.saveRead
  have hwrite₂ : ∀ t < 2, InRegions s₂.wr (State.addr (s₂.gpr .r1 + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [hs₂.2.2.1.wr, hs₁.wr, hregs₂ .r1 (by decide)]
    exact hwrite
  apply WP.mono (blockTail_ok s s₂ direction _ hs₂.1 saved₂
    (by rw [hregs₂ .r2 (by decide)]; exact hp.scratchFit)
    (by rw [hregs₂ .r1 (by decide)]; exact hp.dataFit) savedRead₂ hwrite₂
    (by rw [saveRegion, hregs₂ .r1 (by decide), hregs₂ .r2 (by decide)]; exact hp.dataSeparate))
  intro s₃ hs₃
  refine ⟨?_, ?_, hs₃.saved, hs₃.rd.trans (hs₂.2.2.1.rd.trans hs₁.rd),
    hs₃.wr.trans (hs₂.2.2.1.wr.trans hs₁.wr),
    hs₃.sp.trans (hs₂.2.2.1.sp.trans hs₁.sp),
    fun q hq => (hs₃.regs q hq).trans (hregs₂ q hq), ?_⟩
  · have hresult := hs₃.result
    rw [hregs₂ .r1 (by decide)] at hresult
    exact hresult.trans (blockResult_core keys direction _)
  · rw [hs₃.pointer, hs₂.2.2.2, hp.pointer]
    cases direction <;> simp only [reduceCtorEq, ite_true, ite_false,
      BitVec.add_sub_cancel, BitVec.sub_add_cancel]
  · have hf₁ : Frame (blockRegions s) s.mem s₁.mem := hs₁.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [blockRegions], Region.sub_prefix (by decide)⟩)
    have hf₂ : Frame (blockRegions s) s₁.mem s₂.mem := hs₂.2.2.1.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      refine ⟨⟨State.addr (s.gpr .r2), 512⟩, by simp [blockRegions], ?_⟩
      have hbase := hs₁.regs .r2 (by decide)
      change Region.Sub ⟨State.addr (s₁.gpr .r2) + BitVec.ofNat 64 60, 388⟩ ⟨State.addr (s.gpr .r2), 512⟩
      rw [hbase]
      exact Offset.sub_base _ (by decide))
    have hf₃ : Frame (blockRegions s) s₂.mem s₃.mem := hs₃.frame.sub (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      rw [hregs₂ .r1 (by decide)]
      exact ⟨⟨State.addr (s.gpr .r1), 8⟩, by simp [blockRegions], fun _ h => h⟩)
    exact hf₁.trans (hf₂.trans hf₃)

end VG.Proof.TripleDes.Arm
