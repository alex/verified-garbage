import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSpace
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitSteps

/-! # Initializing both leading blocks of one lane -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Impl.Argon2.X86_64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LaneDone (s t : State) : Prop where
  first : bytesAt t.mem (s.gpr .r14) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat 0
  second : bytesAt t.mem (s.gpr .r14 + 1024) 1024 = Proof.Argon2.initialBytes
    (bytesAt s.mem (s.gpr .rbp) 64) (s.gpr .r12).toNat 1
  destination : t.gpr .r14 = s.gpr .r14 + s.gpr .r13
  lane : t.gpr .r12 = s.gpr .r12 + 1
  remaining : t.gpr .r15 = s.gpr .r15 - 1
  zf : t.zf = some (s.gpr .r15 - 1 == 0)
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r12 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .r14, 2048⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

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

theorem lane_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (memory : Addr) (bytes d : Nat) (space : Space s memory bytes)
    (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d) (bound : d + 2048 ≤ bytes) :
    WP isa (lane name (HPrime.hash v)) s (LaneDone s) := by
  have ready := space.blockReady dst (by omega)
  unfold lane
  refine WP.seq ((block_ok v name s 0 ready).mono ?_)
  intro a ha
  have spaceA := space.same ha.wr (ha.regs .rbp (by decide))
    (ha.regs .rbx (by decide)) (ha.regs .rsp (by decide))
  refine WP.seq ((advance_ok a).mono ?_)
  intro b hb
  have spaceB := spaceA.same hb.wr (hb.other .rbp (by decide))
    (hb.other .rbx (by decide)) (hb.other .rsp (by decide))
  have base : b.gpr .r14 = s.gpr .r14 + 1024 := by rw [hb.destination, ha.regs .r14 (by decide)]
  have bp : b.gpr .rbp = s.gpr .rbp := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have bx : b.gpr .rbx = s.gpr .rbx := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have sp : b.gpr .rsp = s.gpr .rsp := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have laneB : b.gpr .r12 = s.gpr .r12 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have strideB : b.gpr .r13 = s.gpr .r13 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have remainingB : b.gpr .r15 = s.gpr .r15 := (hb.other _ (by decide)).trans (ha.regs _ (by decide))
  have dstB : b.gpr .r14 = memory + BitVec.ofNat 64 (d + 1024) := by
    rw [base, dst, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have readyB := spaceB.blockReady dstB (by omega)
  refine WP.seq ((block_ok v name b 1 readyB).mono ?_)
  intro c hc
  refine (laneEnd_ok c).mono ?_
  intro t ht
  have secondFrame := hc.frame
  rw [base, bx, sp, bp] at secondFrame
  have keptFirst : bytesAt c.mem (s.gpr .r14) 1024 = bytesAt b.mem (s.gpr .r14) 1024 := by
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply secondFrame.bytes (R := ⟨s.gpr .r14, 1024⟩) _
      (show (1024 : Nat) ≤ 2 ^ 64 from by decide) hi
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.base_disjoint _ (by decide) (by decide)
    · rw [dst]; exact space.matrixWork.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.stackMatrix.symm.sub_left (Offset.sub_base _ (by omega))
    · rw [dst]; exact space.frameMatrix.symm.sub_left (Offset.sub_base _ (by omega)) |>.sub_right
        (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
  have h0B : bytesAt b.mem (b.gpr .rbp) 64 = bytesAt s.mem (s.gpr .rbp) 64 := by
    rw [hb.mem, bp]; exact ha.h0 ready
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ht.rd.trans (hc.rd.trans (hb.rd.trans ha.rd)),
    ht.wr.trans (hc.wr.trans (hb.wr.trans ha.wr)), ?_⟩
  · rw [ht.mem, keptFirst, hb.mem]; exact ha.digest
  · have digest := hc.digest
    rw [base, h0B, laneB] at digest
    rw [ht.mem]; exact digest
  · rw [ht.destination, hc.regs .r14 (by decide), hc.regs .r13 (by decide), base, strideB]
    rw [BitVec.add_assoc, BitVec.add_comm (1024 : Addr), ← BitVec.add_assoc,
      BitVec.add_sub_cancel]
  · rw [ht.lane, hc.regs .r12 (by decide), laneB]
  · rw [ht.remaining, hc.regs .r15 (by decide), remainingB]
  · rw [ht.zf, hc.regs .r15 (by decide), remainingB]
  · intro r hr h14 h12 h15
    exact (ht.other r h14 h12 h15).trans ((hc.regs r hr).trans
      ((hb.other r h14).trans (ha.regs r hr)))
  · rw [ht.mem]
    rw [hb.mem] at secondFrame
    have firstFrame := frame_widen (p := s.gpr .r14) (d := 0)
      (by simpa using ha.frame)
      (by decide)
    have finalFrame := frame_widen (p := s.gpr .r14) (d := 1024)
      (by simpa only [show BitVec.ofNat 64 1024 = (1024 : Addr) from rfl] using secondFrame) (by decide)
    exact firstFrame.trans finalFrame

end VG.Proof.Argon2.X86_64.MemoryInit
