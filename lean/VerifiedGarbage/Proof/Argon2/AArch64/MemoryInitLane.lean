import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitSpace
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitSteps

/-! # Initializing both leading blocks of one lane -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LaneDone (s t : State) : Prop where
  first : bytesAt t.mem (s.gpr .x22) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .x19) 64) (s.gpr .x20).toNat 0
  second : bytesAt t.mem (s.gpr .x22 + 1024) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .x19) 64) (s.gpr .x20).toNat 1
  destination : t.gpr .x22 = s.gpr .x22 + s.gpr .x21
  lane : t.gpr .x20 = s.gpr .x20 + 1
  remaining : t.gpr .x23 = s.gpr .x23 - 1
  flag : t.gpr .x15 = s.gpr .x23 - 1
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x22, 2048⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem

theorem frame_widen {m m' : Mem} {p : Addr} {d : Nat} {work stack headRegion : Region}
    (h : Frame [⟨p + BitVec.ofNat 64 d, 1024⟩, work, stack, headRegion] m m')
    (bound : d + 1024 ≤ 2048) : Frame [⟨p, 2048⟩, work, stack, headRegion] m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Offset.sub_base _ bound⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
  · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))), fun _ h => h⟩

theorem lane_ok (v : HPrime.Backend) (name : String)
    (s : State) (memory : Addr) (bytes d : Nat) (space : Space s memory bytes)
    (dst : s.gpr .x22 = memory + BitVec.ofNat 64 d) (bound : d + 2048 ≤ bytes) :
    WP isa (lane name v.hash) s (LaneDone s) := by
  have ready := space.blockReady dst (by omega)
  unfold lane
  refine WP.seq ((block_ok v name s 0 (by decide) ready).mono ?_)
  intro a ha
  have spaceA := space.same ha.wr (ha.regs .x19 (by decide))
    (ha.regs .x24 (by decide)) ha.sp
  refine WP.seq ((advance_ok a).mono ?_)
  intro b hb
  have spaceB := spaceA.same hb.wr (hb.other .x19 (by decide) (by decide) (by decide))
    (hb.other .x24 (by decide) (by decide) (by decide)) hb.sp
  have base : b.gpr .x22 = s.gpr .x22 + 1024 := by rw [hb.destination, ha.regs .x22 (by decide)]
  have bp : b.gpr .x19 = s.gpr .x19 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have bx : b.gpr .x24 = s.gpr .x24 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have sp : b.sp = s.sp := hb.sp.trans ha.sp
  have laneB : b.gpr .x20 = s.gpr .x20 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have strideB : b.gpr .x21 = s.gpr .x21 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have remainingB : b.gpr .x23 = s.gpr .x23 := (hb.other _ (by decide) (by decide) (by decide)).trans (ha.regs _ (by decide))
  have dstB : b.gpr .x22 = memory + BitVec.ofNat 64 (d + 1024) := by
    rw [base, dst, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have readyB := spaceB.blockReady dstB (by omega)
  refine WP.seq ((block_ok v name b 1 (by decide) readyB).mono ?_)
  intro c hc
  refine (laneEnd_ok c).mono ?_
  intro t ht
  have secondFrame := hc.frame
  rw [base, bx, sp, bp] at secondFrame
  have keptFirst : bytesAt c.mem (s.gpr .x22) 1024 = bytesAt b.mem (s.gpr .x22) 1024 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply secondFrame.bytes (R := ⟨s.gpr .x22, 1024⟩) _
      (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · rw [dst]; exact space.matrixWork.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.stackMatrix.symm.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.frameMatrix.symm.sub_left (Offset.sub_base _ (by omega)) |>.sub_right
        (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
  have h0B : bytesAt b.mem (b.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
    rw [hb.mem, bp]; exact ha.h0 ready
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht.sp.trans (hc.sp.trans (hb.sp.trans ha.sp)), ht.rd.trans (hc.rd.trans (hb.rd.trans ha.rd)),
    ht.wr.trans (hc.wr.trans (hb.wr.trans ha.wr)), ?_⟩
  · rw [ht.mem, keptFirst, hb.mem]; exact ha.digest
  · have digest := hc.digest
    rw [base, h0B, laneB] at digest
    rw [ht.mem]; exact digest
  · rw [ht.destination, hc.regs .x22 (by decide), hc.regs .x21 (by decide), base, strideB]
    rw [BitVec.add_assoc, BitVec.add_comm (1024 : Addr), ← BitVec.add_assoc,
      BitVec.add_sub_cancel]
  · rw [ht.lane, hc.regs .x20 (by decide), laneB]
  · rw [ht.remaining, hc.regs .x23 (by decide), remainingB]
  · rw [ht.flag, hc.regs .x23 (by decide), remainingB]
  · intro r hr h14 h12 h15
    have h12temp : r ≠ .x12 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have h15temp : r ≠ .x15 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (ht.other r h14 h12 h15 h12temp h15temp).trans ((hc.regs r hr).trans
      ((hb.other r h14 h12temp h15temp).trans (ha.regs r hr)))
  · rw [ht.mem]
    rw [hb.mem] at secondFrame
    have firstFrame := frame_widen (p := s.gpr .x22) (d := 0)
      (by simpa using ha.frame)
      (by decide)
    have finalFrame := frame_widen (p := s.gpr .x22) (d := 1024)
      (by simpa only [show BitVec.ofNat 64 1024 = (1024 : Addr) from rfl] using secondFrame) (by decide)
    exact firstFrame.trans finalFrame

end VG.Proof.Argon2.AArch64.MemoryInit
