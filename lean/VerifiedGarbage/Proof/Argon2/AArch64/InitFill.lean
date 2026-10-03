import VerifiedGarbage.Impl.Argon2.AArch64.InitFill
import VerifiedGarbage.Proof.Argon2.AArch64.FillFinish
import VerifiedGarbage.Proof.Argon2.AArch64.FillCompressSetup
import VerifiedGarbage.Proof.Argon2.AArch64.FillIterationsBody
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Impl.Argon2.AArch64.FillSetup
import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
import VerifiedGarbage.Proof.Argon2.AArch64.FillIterations
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.RelCT
import VerifiedGarbage.Proof.Argon2.Dimensions
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitLit
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitBlock
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitCall
import VerifiedGarbage.Proof.Argon2.Matrix
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitScale
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitSpace
import VerifiedGarbage.Proof.Argon2.AArch64.InitialLayout
import VerifiedGarbage.Impl.Argon2.AArch64.MemoryInit
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitClearMemory
import VerifiedGarbage.Proof.Argon2.AArch64.Instructions

/-! Merged from `Proof.Argon2.AArch64.MemoryInitSteps`. -/
section
/-! Public pointer advances and lane countdowns. -/
namespace VG.Proof.Argon2.AArch64.MemoryInit
open VG VG.AArch64

structure Advanced (s t : State) : Prop where
  destination : t.gpr .x22 = s.gpr .x22 + 1024
  other : ∀ r, r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem advance_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.addi .x22 1024].flatten) s (Advanced s) := by
  refine (Instructions.addi_ok s .x22 1024 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨value, k⟩
  refine ⟨value, fun r h1 h2 h3 => k.regs r ?_, k.mem, k.rd, k.wr, k.sp⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨h1,h2,h3⟩

structure LaneEnd (s t : State) : Prop where
  destination : t.gpr .x22 = s.gpr .x22 + s.gpr .x21 - 1024
  lane : t.gpr .x20 = s.gpr .x20 + 1
  remaining : t.gpr .x23 = s.gpr .x23 - 1
  flag : t.gpr .x15 = s.gpr .x23 - 1
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem laneEnd_ok (s : State) :
    WP isa (.block [Impl.Argon2.AArch64.Instructions.add .x22 .x21,
      Impl.Argon2.AArch64.Instructions.subi .x22 1024,
      Impl.Argon2.AArch64.Instructions.addi .x20 1,
      Impl.Argon2.AArch64.Instructions.subi .x23 1].flatten) s (LaneEnd s) := by
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [WP.block_append_iff]
  refine (Instructions.add_ok s .x22 .x21 (by decide)).mono ?_
  rintro a ⟨dstA, ka⟩
  rw [WP.block_append_iff]
  refine (Instructions.subi_ok a .x22 1024 (by decide) (by decide) (by decide)).mono ?_
  rintro b ⟨dstB, _, kb⟩
  rw [WP.block_append_iff]
  refine (Instructions.addi_ok b .x20 1 (by decide) (by decide) (by decide)).mono ?_
  rintro c ⟨laneC, kc⟩
  refine (Instructions.subi_ok c .x23 1 (by decide) (by decide) (by decide)).mono ?_
  rintro t ⟨remaining, flag, kt⟩
  have remainingC : c.gpr .x23 = s.gpr .x23 :=
    (kc.regs _ (by decide)).trans ((kb.regs _ (by decide)).trans (ka.regs _ (by decide)))
  refine ⟨?_, ?_, remaining.trans (congrArg (· - 1) remainingC),
    flag.trans (congrArg (· - 1) remainingC), ?_,
    kt.mem.trans (kc.mem.trans (kb.mem.trans ka.mem)),
    kt.rd.trans (kc.rd.trans (kb.rd.trans ka.rd)),
    kt.wr.trans (kc.wr.trans (kb.wr.trans ka.wr)),
    kt.sp.trans (kc.sp.trans (kb.sp.trans ka.sp))⟩
  · rw [kt.regs .x22 (by decide), kc.regs .x22 (by decide), dstB, dstA]; rfl
  · rw [kt.regs .x20 (by decide), laneC, kb.regs .x20 (by decide), ka.regs .x20 (by decide)]; rfl
  · intro r h1 h2 h3 h4 h5
    have hka : r ∉ [Reg.x22, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h5⟩
    have hkb : r ∉ [Reg.x22, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h4,h5⟩
    have hkc : r ∉ [Reg.x20, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h2,h4,h5⟩
    have hkt : r ∉ [Reg.x23, .x12, .x15] := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h3,h4,h5⟩
    exact (kt.regs r hkt).trans ((kc.regs r hkc).trans ((kb.regs r hkb).trans (ka.regs r hka)))
end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitLane`. -/
section
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
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitStage`. -/
section
/-! # Matrix invariant: completed lanes contain their RFC initialization blocks -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def Initialized (m : Mem) (base : Addr) (lanes q done : Nat) (h0 : List Byte) : Prop :=
  ∀ lane < lanes, ∀ column < q,
    blockAt m (base + BitVec.ofNat 64 (1024 * (lane * q + column))) =
      if lane < done ∧ column < 2 then parseBlock (Proof.Argon2.initialBytes h0 lane column)
      else zeroBlock

theorem cell_bound (lanes q lane column : Nat) (hl : lane < lanes) (hc : column < q) :
    lane * q + column < lanes * q := by
  have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ lanes by omega)
  rw [Nat.add_mul, Nat.one_mul] at mul
  omega

theorem cell_sep (q j lane column : Nat) (hq : 2 ≤ q) (hc : column < q)
    (other : lane ≠ j ∨ 2 ≤ column) :
    1024 * (lane * q + column) + 1024 ≤ 1024 * (j * q) ∨
      1024 * (j * q) + 2048 ≤ 1024 * (lane * q + column) := by
  by_cases lt : lane < j
  · have mul := Nat.mul_le_mul_right q (show lane + 1 ≤ j by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  · by_cases gt : j < lane
    · have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lane by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    · have eq : lane = j := by omega
      subst lane
      have large : 2 ≤ column := other.elim (fun h => False.elim (h rfl)) id
      omega

theorem initialized_zero (m : Mem) (base : Addr) (lanes q : Nat)
    (bound : 1024 * (lanes * q) < 2 ^ 64) (h0 : List Byte) :
    Initialized (clearMem m base (128 * (lanes * q))) base lanes q 0 h0 := by
  intro lane hl column hc
  rw [clearMem_block _ _ _ _ bound (cell_bound _ _ _ _ hl hc)]
  simp only [Nat.not_lt_zero, false_and, ite_false]

theorem initialized_lane {s t : State} (memory : Addr) (lanes q j : Nat)
    (h0 : List Byte) (space : Space s memory (1024 * (lanes * q)))
    (hq : 2 ≤ q) (hj : j < lanes) (lanesBound : lanes < 2 ^ 64)
    (dst : s.gpr .x22 = memory + BitVec.ofNat 64 (1024 * (j * q)))
    (laneReg : s.gpr .x20 = BitVec.ofNat 64 j)
    (hash : bytesAt s.mem (s.gpr .x19) 64 = h0)
    (initialized : Initialized s.mem memory lanes q j h0) (done : LaneDone s t) :
    Initialized t.mem memory lanes q (j + 1) h0 := by
  have laneValue : (s.gpr .x20).toNat = j := by
    rw [laneReg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have currentEnd : 1024 * (j * q) + 2048 ≤ 2 ^ 64 := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    have b := space.bound
    omega
  have cellEnd (lane column : Nat) (hl : lane < lanes) (hc : column < q) :
      1024 * (lane * q + column) + 1024 ≤ 2 ^ 64 := by
    have cell := cell_bound lanes q lane column hl hc
    have b := space.bound
    omega
  intro lane hl column hc
  by_cases same : lane = j
  · subst lane
    by_cases first : column = 0
    · subst column
      rw [ite_eq_left (by omega)]
      apply Proof.Argon2.blockAt_of_initialBytes
      have eq := done.first
      rw [hash, laneValue, dst] at eq
      simpa only [Nat.add_zero] using eq
    · by_cases second : column = 1
      · subst column
        rw [ite_eq_left (by omega)]
        apply Proof.Argon2.blockAt_of_initialBytes
        have eq := done.second
        rw [hash, laneValue, dst, BitVec.add_assoc,
          show (1024 : Addr) = BitVec.ofNat 64 1024 from rfl, ← BitVec.ofNat_add] at eq
        rw [Nat.mul_add, Nat.mul_one]
        exact eq
      · have large : 2 ≤ column := by omega
        have sep := cell_sep q j j column hq hc (Or.inr large)
        have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) =
            blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (j * q + column))) := by
          apply blockAt_frame done.frame
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · rw [dst]; exact Offset.disjoint _ sep (cellEnd j column hj hc) currentEnd
          · exact space.matrixWork.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega))
          · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega))
          · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
              (by have := cell_bound lanes q j column hj hc; omega)) |>.sub_right
              (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
        rw [kept, initialized j hj column hc]
        simp only [Nat.lt_irrefl, false_and, ite_false, ite_eq_right (by omega : ¬ (j < j + 1 ∧ column < 2))]
  · have kept : blockAt t.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) =
        blockAt s.mem (memory + BitVec.ofNat 64 (1024 * (lane * q + column))) := by
      apply blockAt_frame done.frame
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [dst]
        exact Offset.disjoint _ (cell_sep q j lane column hq hc (Or.inl same))
          (cellEnd lane column hl hc) currentEnd
      · exact space.matrixWork.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega))
      · exact space.stackMatrix.symm.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega))
      · exact space.frameMatrix.symm.sub_left (Offset.sub_base _
          (by have := cell_bound lanes q lane column hl hc; omega)) |>.sub_right
          (Offset.sub_base _ (by decide : 64 + 8 ≤ 272))
    rw [kept, initialized lane hl column hc]
    by_cases before : lane < j ∧ column < 2 <;>
      simp (disch := omega) only [ite_eq_left, ite_eq_right]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitSetup`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitClearSetup`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitClear`. -/
section
/-! # Zeroing the Argon2 matrix, independently of its initial contents -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

theorem decrement_ok (s : State) :
    WP isa (.block (Impl.Argon2.AArch64.Instructions.subi .x8 1)) s fun t =>
      t.gpr .x8 = s.gpr .x8 - 1 ∧ t.gpr .x15 = s.gpr .x8 - 1 ∧
      Divide.Keeps [.x8, .x12, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.Instructions.subi,
    Impl.Argon2.AArch64.Instructions.sub, Impl.Argon2.AArch64.Instructions.imm,
    Impl.Argon2.AArch64.Instructions.mark, Impl.Argon2.AArch64.Instructions.mov,
    show 1 < 65536 from by decide, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, show 0 < 4096 from by decide, Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (1#16).setWidth 64 = 1#64 from rfl,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, sub_value, Bool.toNat_true,
    BitVec.setWidth_eq, BitVec.add_zero, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem clearWord_ok (s : State) (hw : InRegions s.wr (s.gpr .x22) 8) :
    WP isa (.block clearWord) s fun t =>
      t.mem = s.mem.writeW (s.gpr .x22) (s.gpr .x3) ∧
      t.gpr .x22 = s.gpr .x22 + 8 ∧ t.gpr .x8 = s.gpr .x8 - 1 ∧
      t.gpr .x15 = s.gpr .x8 - 1 ∧
      (∀ r, r ≠ .x8 → r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  simp only [clearWord, List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [WP.block_append_iff]
  have hw' : InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 0) 8 := by
    simpa only [BitVec.add_zero] using hw
  refine (Instructions.store_ok s .x22 .x3 0 (by decide) (by decide) hw').mono ?_
  rintro a ⟨memA, regsA, rdA, wrA, spA⟩
  rw [WP.block_append_iff]
  refine (Instructions.addi_ok a .x22 8 (by decide) (by decide) (by decide)).mono ?_
  rintro b ⟨dst, kb⟩
  refine (decrement_ok b).mono ?_
  rintro t ⟨count, flag, kt⟩
  have countB : b.gpr .x8 = s.gpr .x8 := (kb.regs _ (by decide)).trans (congrFun regsA _)
  refine ⟨?_, ?_, count.trans (congrArg (· - 1) countB),
    flag.trans (congrArg (· - 1) countB), ?_, kt.rd.trans (kb.rd.trans rdA),
    kt.wr.trans (kb.wr.trans wrA), kt.sp.trans (kb.sp.trans spA)⟩
  · rw [kt.mem, kb.mem, memA]
    rw [BitVec.add_zero]
  · rw [kt.regs .x22 (by decide), dst, regsA]
    rfl
  · intro r h1 h2 h3 h4
    exact (kt.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h1,h3,h4⟩)).trans
      ((kb.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨h2,h3,h4⟩)).trans
        (congrFun regsA r))

structure ClearI (s₀ : State) (p : Addr) (n j : Nat) (s : State) : Prop where
  bound : j ≤ n
  destination : s.gpr .x22 = p + BitVec.ofNat 64 (8 * j)
  count : s.gpr .x8 = BitVec.ofNat 64 (n - j)
  zero : s.gpr .x3 = 0
  other : ∀ r, r ≠ .x8 → r ≠ .x22 → r ≠ .x12 → r ≠ .x15 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  mem : s.mem = clearMem s₀.mem p j

theorem clearLoop_ok (s₀ : State) (p : Addr) (n : Nat) (lo : 1 ≤ n)
    (bound : 8 * n < 2 ^ 64) (dst : s₀.gpr .x22 = p)
    (count : s₀.gpr .x8 = BitVec.ofNat 64 n) (zero : s₀.gpr .x3 = 0)
    (write : ∀ j < n, InRegions s₀.wr (p + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (.loop (.block clearWord) (.nonzero .x .x15)) s₀ (ClearI s₀ p n n) := by
  refine WP.loop (M := isa) (fun k s => ∃ j, k = n - j ∧ j < n ∧ ClearI s₀ p n j s)
    ?_ n s₀ ⟨0, by omega, lo, by omega, by simpa using dst, by simpa only [Nat.sub_zero] using count,
      zero, fun _ _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  rintro k s ⟨j, rfl, hj, h⟩
  have hw : InRegions s.wr (s.gpr .x22) 8 := by
    rw [h.wr, h.destination]; exact write j hj
  refine (clearWord_ok s hw).mono ?_
  rintro t ⟨memT, dstT, countT, zfT, otherT, rdT, wrT, spT⟩
  have nextCount : BitVec.ofNat 64 (n - j) - 1 = BitVec.ofNat 64 (n - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : ClearI s₀ p n (j + 1) t := by
    refine ⟨by omega, ?_, ?_, (otherT _ (by decide) (by decide) (by decide) (by decide)).trans h.zero,
      fun r h1 h2 h3 h4 => (otherT r h1 h2 h3 h4).trans (h.other r h1 h2 h3 h4),
      rdT.trans h.rd, wrT.trans h.wr, spT.trans h.sp, ?_⟩
    · rw [dstT, h.destination, BitVec.add_assoc, show (8 : Addr) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
      congr 2
    · rw [countT, h.count, nextCount]
    · rw [memT, h.mem, h.destination, h.zero]; rfl
  have eqzero : BitVec.ofNat 64 (n - (j + 1)) = 0 ↔ n - (j + 1) = 0 := by
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  have flag : eval (.nonzero .x .x15) t = some (decide (n - (j + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, zfT, h.count, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
    exact not_congr eqzero
  by_cases done : j + 1 = n
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show n - (j + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using flag
  · refine .inr ⟨?_, n - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x15) t = some true
    rw [flag]
    exact congrArg some (decide_eq_true (by omega : n - (j + 1) ≠ 0))

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Clearing the complete allocation using its public block count -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure ClearHeader (s t : State) : Prop where
  destination : t.gpr .x22 = wordAt s memoryOffset
  count : t.gpr .x8 = wordAt s blocksOffset
  zero : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clearHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8) :
    WP isa (.block clearHeader) s (ClearHeader s) := by
  have hm : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232#64) 8 := memoryRead
  have hb : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240#64) 8 := blocksRead
  apply WP.of_runBlock
  simp only [clearHeader, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.imm, show 0 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod, memoryOffset, blocksOffset,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, hm, hb, reduceCtorEq, ite_true, ite_false, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r h1 h2 h3 _ _
    simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure ClearSetup (s t : State) : Prop where
  destination : t.gpr .x22 = wordAt s memoryOffset
  count : t.gpr .x8 = wordAt s blocksOffset * 128
  zero : t.gpr .x3 = 0
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clearSetup_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8) :
    WP isa clearSetupCode s (ClearSetup s) := by
  unfold clearSetupCode clearSetup
  rw [WP.block_append_iff]
  refine (clearHeader_ok s memoryRead blocksRead).mono ?_
  intro a ha
  refine (scale_ok a .x8 7).mono ?_
  intro b hb
  exact ⟨(hb.other _ (by decide) (by decide)).trans ha.destination,
    by rw [hb.value, ha.count]; rfl,
    (hb.other _ (by decide) (by decide)).trans ha.zero,
    fun r h1 h2 h3 h4 h5 => (hb.other r h2 h5).trans (ha.other r h1 h2 h3 h4 h5),
    hb.mem.trans ha.mem, hb.rd.trans ha.rd, hb.wr.trans ha.wr, hb.sp.trans ha.sp⟩

structure Cleared (s t : State) (memory : Addr) (blocks : Nat) : Prop where
  destination : t.gpr .x22 = memory + BitVec.ofNat 64 (1024 * blocks)
  other : ∀ r, r ≠ .x22 → r ≠ .x8 → r ≠ .x3 → r ≠ .x12 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = clearMem s.mem memory (128 * blocks)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem clear_ok (s : State) (memory : Addr) (blocks : Nat) (lo : 1 ≤ blocks)
    (bound : 1024 * blocks < 2 ^ 64)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 blocks)
    (cover : Covers [⟨memory, 1024 * blocks⟩] s.wr) :
    WP isa clear s fun t => Cleared s t memory blocks := by
  unfold clear
  refine WP.seq ((clearSetup_ok s memoryRead blocksRead).mono ?_)
  intro b hb
  have count : b.gpr .x8 = BitVec.ofNat 64 (128 * blocks) := by
    rw [hb.count, blocksWord, show (128 : Addr) = BitVec.ofNat 64 128 from rfl,
      ← BitVec.ofNat_mul, Nat.mul_comm]
  have dst : b.gpr .x22 = memory := hb.destination.trans memoryWord
  have zero := hb.zero
  have mem := hb.mem
  have rd := hb.rd
  have wr := hb.wr
  have other := hb.other
  have sp := hb.sp
  refine (clearLoop_ok b memory (128 * blocks) (by omega) (by omega) dst count zero ?_).mono ?_
  · intro j hj
    rw [wr]
    exact cover _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩
  · intro t ht
    refine ⟨?_, fun r h1 h2 h3 h4 h5 => (ht.other r h2 h1 h4 h5).trans (other r h1 h2 h3 h4 h5), ?_,
      ht.rd.trans rd, ht.wr.trans wr, ht.sp.trans sp⟩
    · rw [ht.destination, show 8 * (128 * blocks) = 1024 * blocks by omega]
    · rw [ht.mem, mem]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Set up the public lane loop after matrix clearing -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure LanesHeader (s t : State) : Prop where
  destination : t.gpr .x22 = wordAt s memoryOffset
  lane : t.gpr .x20 = 0
  remaining : t.gpr .x23 = wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lanesHeader_ok (s : State)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8) :
    WP isa (.block lanesHeader) s (LanesHeader s) := by
  have hm : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232#64) 8 := memoryRead
  have hl : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184#64) 8 := lanesRead
  apply WP.of_runBlock
  simp only [lanesHeader, Impl.Argon2.AArch64.Instructions.load,
    Impl.Argon2.AArch64.Instructions.imm, show 0 < 65536 from by decide,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.load, addr,
    Size.bytes, Size.bits, Nat.reduceMul, Nat.reduceLT, Nat.reduceMod, memoryOffset,
    VG.Impl.Argon2.AArch64.Initial.lanesOffset,
    BitVec.shiftLeft_zero, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.setWidth_eq, hm, hl, reduceCtorEq, ite_true, ite_false, and_self,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]; rfl
  · simp only [RegUpd.gpr_write, ite_true]; rfl
  · intro r h1 h2 h3 _
    simp only [RegUpd.gpr_write, h1, h2, h3, ite_false]
  · simp only [RegUpd.mem_write]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

structure Setup (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  destination : t.gpr .x22 = memory
  lane : t.gpr .x20 = 0
  remaining : t.gpr .x23 = BitVec.ofNat 64 lanes
  stride : t.gpr .x21 = BitVec.ofNat 64 (1024 * q)
  other : ∀ r, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x21 → r ≠ .x15 → t.gpr r = s.gpr r
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem lanesSetup_ok (s : State) (memory : Addr) (lanes q : Nat)
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (lanesWord : wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (laneLength : s.gpr .x21 = BitVec.ofNat 64 q) :
    WP isa (.block lanesSetup) s fun t => Setup s t memory lanes q := by
  unfold lanesSetup
  rw [WP.block_append_iff]
  refine (lanesHeader_ok s memoryRead lanesRead).mono ?_
  intro a ha
  refine (scale_ok a .x21 10).mono ?_
  intro t ht
  refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => (ht.other r h4 h5).trans (ha.other r h1 h2 h3 h5),
    ht.mem.trans ha.mem, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ht.sp.trans ha.sp⟩
  · rw [ht.other .x22 (by decide) (by decide), ha.destination, memoryWord]
  · rw [ht.other .x20 (by decide) (by decide), ha.lane]
  · rw [ht.other .x23 (by decide) (by decide), ha.remaining, lanesWord]
  · rw [ht.value, ha.other .x21 (by decide) (by decide) (by decide) (by decide), laneLength,
      ← BitVec.ofNat_mul, Nat.mul_comm]

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitLoop`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitFrame`. -/
section
/-! # Effects allowed across the complete lane loop -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64
open VG.Spec.Blake2 (bytesAt)

def keptRegs : List Reg := [.x19, .x24, .x21, .x25, .x26, .x27, .x28]

structure Keeps (s t : State) (memory : Addr) (bytes : Nat) : Prop where
  regs : ∀ r ∈ keptRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, bytes⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem

theorem Keeps.x19 {s t : State} {memory : Addr} {bytes : Nat} (h : Keeps s t memory bytes) :
    t.gpr .x19 = s.gpr .x19 := h.regs _ (by decide)
theorem Keeps.x24 {s t : State} {memory : Addr} {bytes : Nat} (h : Keeps s t memory bytes) :
    t.gpr .x24 = s.gpr .x24 := h.regs _ (by decide)
theorem Keeps.refl (s : State) (memory : Addr) (bytes : Nat) : Keeps s s memory bytes :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem Keeps.trans {s t u : State} {memory : Addr} {bytes : Nat}
    (h : Keeps s t memory bytes) (k : Keeps t u memory bytes) : Keeps s u memory bytes :=
  ⟨fun r hr => (k.regs r hr).trans (h.regs r hr), k.sp.trans h.sp, k.rd.trans h.rd, k.wr.trans h.wr,
    h.frame.trans (by simpa only [h.x24, h.sp, h.x19] using k.frame)⟩

theorem Space.keeps {s t : State} {memory : Addr} {bytes : Nat}
    (h : Space s memory bytes) (k : Keeps s t memory bytes) : Space t memory bytes :=
  h.same k.wr k.x19 k.x24 k.sp

theorem Keeps.h0 {s t : State} {memory : Addr} {bytes : Nat}
    (h : Keeps s t memory bytes) (space : Space s memory bytes) :
    bytesAt t.mem (t.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
  rw [h.x19]
  apply Proof.Blake2.bytesAt_congr
  intro i hi
  apply h.frame.bytes (R := ⟨s.gpr .x19, 64⟩) _
    (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact space.frameMatrix.sub_left (Region.sub_prefix (by decide))
  · exact space.frameWork.sub_left (Region.sub_prefix (by decide))
  · exact space.stackFrame.symm.sub_left (Region.sub_prefix (by decide))
  · exact Offset.base_disjoint _ (by decide) (by decide)

theorem LaneDone.keeps {s t : State} (memory : Addr) (bytes d : Nat)
    (h : LaneDone s t) (dst : s.gpr .x22 = memory + BitVec.ofNat 64 d)
    (bound : d + 2048 ≤ bytes) : Keeps s t memory bytes := by
  refine ⟨?_, h.sp, h.rd, h.wr, ?_⟩
  · intro r hr
    have facts : ∀ r ∈ keptRegs, r ∈ FillCompress.loopRegs ∧ r ≠ .x22 ∧ r ≠ .x20 ∧ r ≠ .x23 := by decide
    obtain ⟨cs, h14, h12, h15⟩ := facts r hr
    exact h.regs r cs h14 h12 h15
  · apply h.frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by rw [dst]; exact Offset.sub_base _ bound⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), fun _ h => h⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_singleton_self _))), fun _ h => h⟩

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Termination and correctness of the all-lanes initialization loop -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopI (s₀ : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte) (s : State) : Prop where
  bound : j ≤ lanes
  destination : s.gpr .x22 = memory + BitVec.ofNat 64 (1024 * (j * q))
  lane : s.gpr .x20 = BitVec.ofNat 64 j
  remaining : s.gpr .x23 = BitVec.ofNat 64 (lanes - j)
  stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * q)
  keeps : Keeps s₀ s memory (1024 * (lanes * q))
  initialized : Initialized s.mem memory lanes q j h0
  hash : bytesAt s.mem (s.gpr .x19) 64 = h0

theorem lane_step (v : HPrime.Backend) (name : String)
    (s₀ s : State) (memory : Addr) (lanes q j : Nat) (h0 : List Byte)
    (space : Space s₀ memory (1024 * (lanes * q))) (hj : j < lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (h : LoopI s₀ memory lanes q j h0 s) :
    WP isa (lane name v.hash) s fun t =>
      LoopI s₀ memory lanes q (j + 1) h0 t ∧
      eval (.nonzero .x .x15) t = some (decide (lanes - (j + 1) ≠ 0)) := by
  have spaceS := space.keeps h.keeps
  have endBound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
    have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
    rw [Nat.add_mul, Nat.one_mul] at mul
    omega
  refine (lane_ok v name s memory (1024 * (lanes * q)) (1024 * (j * q))
    spaceS h.destination endBound).mono ?_
  intro t ht
  have kt := ht.keeps memory _ _ h.destination endBound
  have nextCount : BitVec.ofNat 64 (lanes - j) - 1 = BitVec.ofNat 64 (lanes - (j + 1)) := by
    rw [show (1 : Addr) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]
    congr 1
  have next : LoopI s₀ memory lanes q (j + 1) h0 t := by
    refine ⟨by omega, ?_, ?_, ?_, ?_, h.keeps.trans kt,
      initialized_lane memory lanes q j h0 spaceS hq hj lanesBound h.destination h.lane
        h.hash h.initialized ht, (kt.h0 spaceS).trans h.hash⟩
    · rw [ht.destination, h.destination, h.stride, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.add_mul, Nat.one_mul, Nat.mul_add]
    · rw [ht.lane, h.lane, BitVec.ofNat_add]; rfl
    · rw [ht.remaining, h.remaining, nextCount]
    · exact (kt.regs .x21 (by decide)).trans h.stride
  have eqzero : BitVec.ofNat 64 (lanes - (j + 1)) = 0 ↔ lanes - (j + 1) = 0 := by
    constructor
    · intro eq
      have num := congrArg BitVec.toNat eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : lanes - (j + 1) < 2 ^ 64),
        show (0 : Addr).toNat = 0 from rfl] using num
    · intro eq; rw [eq]; rfl
  have zf : eval (.nonzero .x .x15) t = some (decide (lanes - (j + 1) ≠ 0)) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, ht.flag, h.remaining, nextCount]
    congr 1
    rw [Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff]
    exact not_congr eqzero
  exact ⟨next, zf⟩


theorem lanesLoop_ok (v : HPrime.Backend) (name : String)
    (s₀ : State) (memory : Addr) (lanes q : Nat) (h0 : List Byte)
    (space : Space s₀ memory (1024 * (lanes * q))) (lo : 1 ≤ lanes)
    (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q)
    (dst : s₀.gpr .x22 = memory) (laneReg : s₀.gpr .x20 = 0)
    (remaining : s₀.gpr .x23 = BitVec.ofNat 64 lanes)
    (stride : s₀.gpr .x21 = BitVec.ofNat 64 (1024 * q))
    (initialized : Initialized s₀.mem memory lanes q 0 h0)
    (hash : bytesAt s₀.mem (s₀.gpr .x19) 64 = h0) :
    WP isa (.loop (lane name v.hash) (.nonzero .x .x15)) s₀ (LoopI s₀ memory lanes q lanes h0) := by
  refine WP.loop (M := isa)
    (fun n s => ∃ j, n = lanes - j ∧ j < lanes ∧ LoopI s₀ memory lanes q j h0 s)
    ?_ lanes s₀ ⟨0, by omega, lo, by omega, by simpa using dst, laneReg,
      by simpa only [Nat.sub_zero] using remaining, stride, Keeps.refl _ _ _, initialized, hash⟩
  rintro n s ⟨j, rfl, hj, h⟩
  refine (lane_step v name s₀ s memory lanes q j h0 space hj lanesBound hq h).mono ?_
  intro t ⟨next, zf⟩
  by_cases done : j + 1 = lanes
  · refine .inl ⟨?_, done ▸ next⟩
    simpa only [show lanes - (j + 1) = 0 by omega, ne_eq, not_true_eq_false, decide_false] using zf
  · refine .inr ⟨?_, lanes - (j + 1), by omega, j + 1, rfl, by omega, next⟩
    change eval (.nonzero .x .x15) t = some true
    rw [zf]
    exact congrArg some (decide_eq_true (by omega : lanes - (j + 1) ≠ 0))

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInit`. -/
section
/-! # Functional correctness of complete memory initialization -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)
open VG.Spec.Blake2 (bytesAt)

theorem Cleared.frame {s t : State} {memory : Addr} {blocks : Nat}
    (h : Cleared s t memory blocks) (bound : 1024 * blocks < 2 ^ 64) :
    Frame [⟨memory, 1024 * blocks⟩] s.mem t.mem := by
  rw [h.mem]
  simpa only [show 8 * (128 * blocks) = 1024 * blocks by omega] using
    clearMem_frame s.mem memory (128 * blocks) (by omega)

theorem Cleared.word {s t : State} {memory : Addr} {blocks d : Nat}
    (h : Cleared s t memory blocks) (space : Space s memory (1024 * blocks))
    (offset : d + 8 ≤ 272) : wordAt t d = wordAt s d := by
  unfold wordAt
  rw [h.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)]
  apply (h.frame space.bound).readW (r := ⟨s.gpr .x19, 272⟩)
    (Offset.contains_base _ offset (by omega)) ?_ (by decide)
  intro r hr; simp only [List.mem_singleton] at hr; subst r
  exact space.frameMatrix

theorem code_ok (v : HPrime.Backend) (name : String)
    (s : State) (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (hq : 2 ≤ q)
    (lanesBound : lanes < 2 ^ 64) (space : Space s memory (1024 * (lanes * q)))
    (memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8)
    (lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8)
    (blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8)
    (memoryWord : wordAt s memoryOffset = memory)
    (lanesWord : wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes)
    (blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q))
    (laneLength : s.gpr .x21 = BitVec.ofNat 64 q) :
    WP isa (code name v.hash) s fun t =>
      Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .x19) 64) ∧
      t.gpr .x19 = s.gpr .x19 ∧ t.gpr .x24 = s.gpr .x24 ∧ t.sp = s.sp ∧
      t.gpr .x21 = BitVec.ofNat 64 (1024 * q) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .x24, 16384⟩,
        below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem ∧
      (∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r) := by
  unfold code lanesSetupCode
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  refine WP.seq ((clear_ok s memory (lanes * q) blocksPositive space.bound memoryRead
    blocksRead memoryWord blocksWord space.matrix).mono ?_)
  intro a ha
  have bpA := ha.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bxA := ha.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have spA := ha.sp
  have spaceA := space.same ha.wr bpA bxA spA
  have hashA : bytesAt a.mem (a.gpr .x19) 64 = bytesAt s.mem (s.gpr .x19) 64 := by
    rw [bpA]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    exact (ha.frame space.bound).bytes (R := ⟨s.gpr .x19, 64⟩) (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact space.frameMatrix.sub_left (Region.sub_prefix (by decide)))
      (show (64 : Nat) ≤ 2 ^ 64 from by decide) hi
  refine WP.seq ((lanesSetup_ok a memory lanes q
    (by rw [ha.rd, ha.wr, bpA]; exact memoryRead)
    (by rw [ha.rd, ha.wr, bpA]; exact lanesRead)
    ((ha.word space (by decide)).trans memoryWord)
    ((ha.word space (by decide)).trans lanesWord)
    ((ha.other .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans laneLength)).mono ?_)
  intro b hb
  have bpB := hb.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bxB := hb.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have spB := hb.sp
  have spaceB := spaceA.same hb.wr bpB bxB spB
  refine (lanesLoop_ok v name b memory lanes q (bytesAt s.mem (s.gpr .x19) 64)
    spaceB lo lanesBound hq hb.destination hb.lane hb.remaining hb.stride ?_ ?_).mono ?_
  · rw [hb.mem, ha.mem]
    exact initialized_zero s.mem memory lanes q space.bound _
  · rw [hb.mem, bpB]; exact hashA
  · intro t ht
    refine ⟨ht.initialized, ht.keeps.x19.trans (bpB.trans bpA),
      ht.keeps.x24.trans (bxB.trans bxA), ht.keeps.sp.trans (spB.trans spA),
      (ht.keeps.regs .x21 (by decide)).trans hb.stride, ht.keeps.rd.trans (hb.rd.trans ha.rd), ht.keeps.wr.trans (hb.wr.trans ha.wr), ?_⟩
    have unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r := by
      intro r hr
      have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
          r ∈ keptRegs ∧ r ≠ .x22 ∧ r ≠ .x8 ∧ r ≠ .x3 ∧ r ≠ .x12 ∧ r ≠ .x15 ∧
          r ≠ .x20 ∧ r ≠ .x23 ∧ r ≠ .x21 := by decide
      obtain ⟨member, h22, h8, h3, h12, h15, h20, h23, h21⟩ := facts r hr
      exact (ht.keeps.regs r member).trans
        ((hb.other r h22 h20 h23 h21 h15).trans (ha.other r h22 h8 h3 h12 h15))
    have fb : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .x24, 16384⟩,
        below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem b.mem := by
      rw [hb.mem]
      exact (ha.frame space.bound).mono (by
        intro r hr
        simp only [List.mem_singleton] at hr
        subst r
        exact List.mem_cons_self ..)
    refine ⟨?_, unused⟩
    apply fb.trans
    have f := ht.keeps.frame
    rw [bpB, bpA, bxB, bxA, spB, spA] at f
    exact f

/-- Every cell agrees with the reviewed initialization spec, in lane-major order. -/
theorem Initialized.spec {m : Mem} {base : Addr} {p : Spec.Argon2.Params}
    {h0 : List Byte} (hl : 0 < p.lanes) (hq : 0 < p.laneLen)
    (h : Initialized m base p.lanes p.laneLen p.lanes h0)
    (k : Nat) (hk : k < p.blocks) :
    Spec.Argon2.blockAt m (base + BitVec.ofNat 64 (1024 * k)) =
      (Spec.Argon2.initMemory p h0).memory[k]'(by
        rw [Proof.Argon2.initMemory_size]; exact hk) := by
  have blocks := Proof.Argon2.blocks_lanes p hl
  have lane : k / p.laneLen < p.lanes := by
    apply (Nat.div_lt_iff_lt_mul hq).mpr
    simpa only [blocks] using hk
  have cell := h (k / p.laneLen) lane (k % p.laneLen) (Nat.mod_lt _ hq)
  rw [Nat.mul_comm (k / p.laneLen) p.laneLen, Nat.div_add_mod] at cell
  simp only [lane, true_and] at cell
  rw [Proof.Argon2.initMemory_cell p h0 k hk]
  exact cell

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitRepresent`. -/
section
/-! Memory initialization establishes the shared matrix representation invariant. -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.Spec.Argon2

theorem Initialized.represents {m : Mem} {base : Addr} {p : Params} {h0 : List Byte}
    (positive : 0 < p.lanes) (lanePositive : 0 < p.laneLen)
    (h : Initialized m base p.lanes p.laneLen p.lanes h0) :
    Proof.Argon2.Represents m base p.blocks (initMemory p h0).memory := by
  refine ⟨Proof.Argon2.initMemory_size p h0, ?_⟩
  intro k hk
  rw [Array.getElem?_eq_getElem (by rw [Proof.Argon2.initMemory_size]; exact hk), Option.getD_some]
  unfold Proof.Argon2.matrixCell
  rw [Nat.mul_comm k 1024]
  exact h.spec positive lanePositive k hk

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitBlockCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitCallCT`. -/
section
/-! # Initialization's H′ calls leak only their public argument registers -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64
open VG.Impl.Argon2.AArch64.HPrime (code)

theorem hPrime_call_rel (v : HPrime.Backend) (name : String)
    {P : State → State → Prop}
    (pre : ∀ s t, P s t → CallReady s ∧ CallReady t ∧
      s.gpr .x1 = 72 ∧ t.gpr .x1 = 72 ∧ s.gpr .x3 = 1024 ∧ t.gpr .x3 = 1024 ∧
      s.gpr .x0 = t.gpr .x0 ∧ s.gpr .x2 = t.gpr .x2 ∧
      s.gpr .x4 = t.gpr .x4 ∧ s.sp = t.sp) :
    RelCT isa P (.call name (code v.hash)) (fun _ _ => True) := by
  apply RelCT.callEx (k := HPrime.localContract) (HPrime.code_correct v) (HPrime.code_ct v)
  intro s t hp
  obtain ⟨hs, ht, ls, lt, os, ot, di, dx, r8, sp⟩ := pre s t hp
  obtain ⟨ps, cs, ws⟩ := hPrime_call_hyps s hs ls os
  obtain ⟨pt, ct, wt⟩ := hPrime_call_hyps t ht lt ot
  refine ⟨_, _, _, _, ps, pt, ?_, cs, ws, ct, wt⟩
  change s.callEntry.gpr .x0 = t.callEntry.gpr .x0 ∧
    s.callEntry.gpr .x1 = t.callEntry.gpr .x1 ∧
    s.callEntry.gpr .x2 = t.callEntry.gpr .x2 ∧
    s.callEntry.gpr .x3 = t.callEntry.gpr .x3 ∧
    s.callEntry.gpr .x4 = t.callEntry.gpr .x4 ∧
    s.callEntry.sp = t.callEntry.sp
  simp only [State.callEntry_gpr _ (by decide : Reg.x0 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x1 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x2 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x3 ∉ linkRegs),
    State.callEntry_gpr _ (by decide : Reg.x4 ∉ linkRegs), State.callEntry_sp]
  exact ⟨di, ls.trans lt.symm, dx, os.trans ot.symm, r8, sp⟩

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Public registers survive each initialization H′ call -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

def savedRegs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24]

def AgreeSaved (s t : State) : Prop := HPrime.AgreeRegs savedRegs s t

theorem blockArgs_rel (column : Nat)
    (ct : ∃ hint, (taint.check (Taint.ofRegs savedRegs)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa AgreeSaved (.block (blockArgs column)) (fun _ _ => True) := by
  obtain ⟨_, check⟩ := ct
  exact RelCT.taint (A := taint) (Taint.ofRegs savedRegs)
    (fun _ _ h => h.taint) check

theorem block_rel (v : HPrime.Backend) (name : String) (column : Nat) (columnBound : column < 65536)
    (ct : ∃ hint, (taint.check (Taint.ofRegs savedRegs)
      (.block (blockArgs column)) hint).isSome = true) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name v.hash column) AgreeSaved := by
  let P := fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t
  have args := ((blockArgs_rel column ct).mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t hp => by
      exact ⟨blockArgs_ok s column columnBound (hp.1.prefix 64 (by decide)) (hp.1.prefix 68 (by decide)),
        blockArgs_ok t column columnBound (hp.2.1.prefix 64 (by decide)) (hp.2.1.prefix 68 (by decide))⟩)
  have call := hPrime_call_rel v name (P := fun a b =>
      True ∧ ∃ s t, P s t ∧ BlockArgs s a column ∧ BlockArgs t b column) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.ready hp.1, hb.ready hp.2.1, ha.inputLength, hb.inputLength,
      ha.outputLength, hb.outputLength, ?_, ?_, ?_, ?_⟩
    · exact ha.input.trans ((hp.2.2.2 .x19 (by decide)).trans hb.input.symm)
    · exact ha.output.trans ((hp.2.2.2 .x22 (by decide)).trans hb.output.symm)
    · exact ha.work.trans ((hp.2.2.2 .x24 (by decide)).trans hb.work.symm)
    · exact ha.sp.trans (hp.2.2.1.trans hb.sp.symm))
  have full := (args.seq call).wpDep (fun s t hp =>
    ⟨block_ok v name s column columnBound hp.1, block_ok v name t column columnBound hp.2.1⟩)
  exact full.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, s, t, hp, ha, hb⟩ := h
    refine ⟨ha.sp.trans (hp.2.2.1.trans hb.sp.symm), ?_⟩
    intro r hr
    have saved : ∀ r ∈ savedRegs, r ∈ FillCompress.loopRegs := by decide
    exact (ha.regs r (saved r hr)).trans ((hp.2.2.2 r hr).trans (hb.regs r (saved r hr)).symm))

theorem blocks_rel (v : HPrime.Backend) (name : String) :
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name v.hash 0) AgreeSaved ∧
    RelCT isa (fun s t => BlockReady s ∧ BlockReady t ∧ AgreeSaved s t)
      (block name v.hash 1) AgreeSaved :=
  ⟨block_rel v name 0 (by decide) ⟨_, by taint_decide⟩,
    block_rel v name 1 (by decide) ⟨_, by taint_decide⟩⟩

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitLoopCT`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitLaneCT`. -/
section
/-! # The two leading blocks of a lane have a public execution trace -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

structure LaneReady (memory : Addr) (bytes d : Nat) (s : State) : Prop where
  space : Space s memory bytes
  destination : s.gpr .x22 = memory + BitVec.ofNat 64 d

def RelatedLane (memory : Addr) (bytes d : Nat) (s t : State) : Prop :=
  LaneReady memory bytes d s ∧ LaneReady memory bytes d t ∧ AgreeSaved s t

theorem BlockDone.laneReady {s t : State} {column : Nat} {memory : Addr} {bytes d : Nat}
    (h : BlockDone s t column) (ready : LaneReady memory bytes d s) :
    LaneReady memory bytes d t :=
  ⟨ready.space.same h.wr (h.regs .x19 (by decide)) (h.regs .x24 (by decide))
    h.sp, (h.regs .x22 (by decide)).trans ready.destination⟩

theorem block_lane_rel (v : HPrime.Backend) (name : String) (column : Nat) (columnBound : column < 65536)
    (ct : ∃ hint, (taint.check (Taint.ofRegs savedRegs)
      (.block (blockArgs column)) hint).isSome = true)
    (memory : Addr) (bytes d : Nat) (bound : d + 1024 ≤ bytes) :
    RelCT isa (RelatedLane memory bytes d) (block name v.hash column)
      (RelatedLane memory bytes d) := by
  have h := ((block_rel v name column columnBound ct).mono
    (P' := RelatedLane memory bytes d) (fun _ _ hp =>
      ⟨hp.1.space.blockReady hp.1.destination bound,
        hp.2.1.space.blockReady hp.2.1.destination bound, hp.2.2⟩)
    (fun _ _ h => h)).wpDep (fun s t hp =>
      ⟨block_ok v name s column columnBound (hp.1.space.blockReady hp.1.destination bound),
        block_ok v name t column columnBound (hp.2.1.space.blockReady hp.2.1.destination bound)⟩)
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ha.laneReady hp.1, hb.laneReady hp.2.1, pub⟩)

theorem advance_rel : RelCT isa AgreeSaved
    (.block ([Impl.Argon2.AArch64.Instructions.addi .x22 1024].flatten)) AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs savedRegs)
    (fun _ _ h => h.taint) savedRegs
  taint_decide

theorem advance_lane_rel (memory : Addr) (bytes d : Nat) :
    RelCT isa (RelatedLane memory bytes d) (.block ([Impl.Argon2.AArch64.Instructions.addi .x22 1024].flatten))
      (RelatedLane memory bytes (d + 1024)) := by
  have h := (advance_rel.mono (P' := RelatedLane memory bytes d)
    (fun _ _ h => h.2.2) (fun _ _ h => h)).wpDep
    (fun s t _ => ⟨advance_ok s, advance_ok t⟩)
  have ready {s t : State} (h : Advanced s t) (hs : LaneReady memory bytes d s) :
      LaneReady memory bytes (d + 1024) t := by
    refine ⟨hs.space.same h.wr (h.other .x19 (by decide) (by decide) (by decide))
      (h.other .x24 (by decide) (by decide) (by decide)) h.sp, ?_⟩
    rw [h.destination, hs.destination, BitVec.ofNat_add, BitVec.add_assoc]; rfl
  exact h.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨pub, s, t, hp, ha, hb⟩ := h
    exact ⟨ready ha hp.1, ready hb hp.2.1, pub⟩)

theorem laneEnd_rel : RelCT isa AgreeSaved
    (.block ([Impl.Argon2.AArch64.Instructions.add .x22 .x21, Impl.Argon2.AArch64.Instructions.subi .x22 1024,
      Impl.Argon2.AArch64.Instructions.addi .x20 1, Impl.Argon2.AArch64.Instructions.subi .x23 1].flatten)) AgreeSaved := by
  apply RelCT.taintRegs (τ := Taint.ofRegs savedRegs)
    (fun _ _ h => h.taint) savedRegs
  taint_decide

theorem lane_rel (v : HPrime.Backend) (name : String)
    (memory : Addr) (bytes d : Nat) (bound : d + 2048 ≤ bytes) :
    RelCT isa (RelatedLane memory bytes d) (lane name v.hash) AgreeSaved := by
  exact (block_lane_rel v name 0 (by decide) ⟨_, by taint_decide⟩ memory bytes d (by omega)).seq
    ((advance_lane_rel memory bytes d).seq
    ((block_lane_rel v name 1 (by decide) ⟨_, by taint_decide⟩ memory bytes (d + 1024) (by omega)).seq
      (laneEnd_rel.mono (fun _ _ h => h.2.2) (fun _ _ h => h))))

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! # Both initialization loops count only pubNext matrix dimensions -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit

theorem lanesLoop_rel (v : HPrime.Backend) (name : String)
    (s₁ s₂ : State) (memory : Addr) (lanes q : Nat) (h₁ h₂ : List Byte)
    (space₁ : Space s₁ memory (1024 * (lanes * q)))
    (space₂ : Space s₂ memory (1024 * (lanes * q)))
    (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (hq : 2 ≤ q) :
    RelCT isa (fun s t => LoopI s₁ memory lanes q 0 h₁ s ∧
      LoopI s₂ memory lanes q 0 h₂ t ∧ AgreeSaved s t)
      (.loop (lane name v.hash) (.nonzero .x .x15)) AgreeSaved := by
  let I := fun n s t => ∃ j, n = lanes - j ∧ j < lanes ∧
    LoopI s₁ memory lanes q j h₁ s ∧ LoopI s₂ memory lanes q j h₂ t ∧ AgreeSaved s t
  have steps : ∀ n, RelCT isa (I n) (lane name v.hash) fun a b =>
      isa.eval (.nonzero .x .x15) a = isa.eval (.nonzero .x .x15) b ∧
      (isa.eval (.nonzero .x .x15) a = some false → AgreeSaved a b) ∧
      (isa.eval (.nonzero .x .x15) a = some true → ∃ m < n, I m a b) := by
    intro n s t trace₁ trace₂ a b hp e₁ e₂
    obtain ⟨j, rfl, hj, hs, ht, pub⟩ := hp
    have bound : 1024 * (j * q) + 2048 ≤ 1024 * (lanes * q) := by
      have mul := Nat.mul_le_mul_right q (show j + 1 ≤ lanes by omega)
      rw [Nat.add_mul, Nat.one_mul] at mul
      omega
    have related : RelatedLane memory (1024 * (lanes * q)) (1024 * (j * q)) s t :=
      ⟨⟨space₁.keeps hs.keeps, hs.destination⟩,
        ⟨space₂.keeps ht.keeps, ht.destination⟩, pub⟩
    obtain ⟨trace, pubNext⟩ := lane_rel v name memory _ _ bound _ _ _ _ _ _ related e₁ e₂
    obtain ⟨_, a', ea, ha⟩ := lane_step v name s₁ s memory lanes q j h₁
      space₁ hj lanesBound hq hs
    obtain ⟨_, b', eb, hb⟩ := lane_step v name s₂ t memory lanes q j h₂
      space₂ hj lanesBound hq ht
    obtain ⟨-, rfl⟩ := Exec.det e₁ ea
    obtain ⟨-, rfl⟩ := Exec.det e₂ eb
    refine ⟨trace, ?_, fun _ => pubNext, ?_⟩
    · simp only [ha.2, hb.2]
    · intro taken
      have remaining : lanes - (j + 1) ≠ 0 := by
        intro zero
        have flag := ha.2
        change eval (.nonzero .x .x15) a = some true at taken
        rw [taken] at flag
        simp only [zero, ne_eq, not_true_eq_false, decide_false, Option.some.injEq, Bool.true_eq_false] at flag
      exact ⟨lanes - (j + 1), by omega, j + 1, rfl, by omega, ha.1, hb.1, pubNext⟩
  exact (RelCT.loop I steps lanes).mono (fun _ _ hp =>
    ⟨0, by omega, lo, hp.1, hp.2.1, hp.2.2⟩) (fun _ _ h => h)

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitDone`. -/
section
/-! Merged from `Proof.Argon2.AArch64.MemoryInitClearCT`. -/
section
/-! # Matrix clearing uses only public addresses and the public allocation size -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Proof.Argon2.AArch64.Initial (wordAt)

structure Ready (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : Space s memory (1024 * (lanes * q))
  memoryRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 232) 8
  lanesRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 184) 8
  blocksRead : InRegions (s.rd ++ s.wr) (s.gpr .x19 + 240) 8
  memoryWord : wordAt s memoryOffset = memory
  lanesWord : wordAt s VG.Impl.Argon2.AArch64.Initial.lanesOffset = BitVec.ofNat 64 lanes
  blocksWord : wordAt s blocksOffset = BitVec.ofNat 64 (lanes * q)
  laneLength : s.gpr .x21 = BitVec.ofNat 64 q

def publicBases : List Reg := [.x19, .x24, .x21]

def AgreeBases (s t : State) : Prop := HPrime.AgreeRegs publicBases s t

theorem clearSetup_rel : RelCT isa AgreeBases clearSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs publicBases)
    (fun _ _ h => h.taint) (by taint_decide)

theorem clearLoop_rel : RelCT isa
    (fun s t => VG.AArch64.Taint.Agree (Taint.ofRegs (.x8 :: .x22 :: publicBases)) s t)
    (.loop (.block clearWord) (.nonzero .x .x15)) AgreeBases := by
  apply RelCT.taintRegs (τ := Taint.ofRegs (.x8 :: .x22 :: publicBases))
    (fun _ _ h => h) publicBases
  taint_decide

theorem clear_rel (memory : Addr) (lanes q : Nat) :
    RelCT isa (fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t)
      clear AgreeBases := by
  let P := fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t
  have prep := (clearSetup_rel.mono (P' := P) (fun _ _ h => h.2.2)
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨clearSetup_ok s h.1.memoryRead h.1.blocksRead,
        clearSetup_ok t h.2.1.memoryRead h.2.1.blocksRead⟩)
  refine prep.seq (clearLoop_rel.mono ?_ (fun _ _ h => h))
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨ha.sp.trans (hp.2.2.1.trans hb.sp.symm), ?_⟩
  intro r hr
  have hr := RegSet.mem_ofList.mp hr
  simp only [List.mem_cons] at hr
  rcases hr with rfl | rfl | hr
  · rw [ha.count, hb.count, hp.1.blocksWord, hp.2.1.blocksWord]
  · rw [ha.destination, hb.destination, hp.1.memoryWord, hp.2.1.memoryWord]
  · have excluded : ∀ r ∈ publicBases, r ≠ .x22 ∧ r ≠ .x8 ∧ r ≠ .x3 ∧ r ≠ .x12 ∧ r ≠ .x15 := by decide
    have hn := excluded r hr
    exact (ha.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).trans
      ((hp.2.2.2 r hr).trans (hb.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2).symm)

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.MemoryInitCT`. -/
section
/-! # The complete memory initialization trace depends only on public parameters -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure LoopReady (memory : Addr) (lanes q : Nat) (s : State) : Prop where
  space : Space s memory (1024 * (lanes * q))
  initialized : Initialized s.mem memory lanes q 0 (bytesAt s.mem (s.gpr .x19) 64)
  destination : s.gpr .x22 = memory
  lane : s.gpr .x20 = 0
  remaining : s.gpr .x23 = BitVec.ofNat 64 lanes
  stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * q)

theorem Cleared.ready {s t : State} {memory : Addr} {lanes q : Nat}
    (h : Cleared s t memory (lanes * q)) (hs : Ready memory lanes q s) :
    Ready memory lanes q t := by
  have bp := h.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have bx := h.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)
  have sp := h.sp
  refine ⟨hs.space.same h.wr bp bx sp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h.rd, h.wr, bp]; exact hs.memoryRead
  · rw [h.rd, h.wr, bp]; exact hs.lanesRead
  · rw [h.rd, h.wr, bp]; exact hs.blocksRead
  · exact (h.word hs.space (by decide)).trans hs.memoryWord
  · exact (h.word hs.space (by decide)).trans hs.lanesWord
  · exact (h.word hs.space (by decide)).trans hs.blocksWord
  · exact (h.other .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs.laneLength

theorem Setup.loopReady {s a b : State} {memory : Addr} {lanes q : Nat}
    (hs : Ready memory lanes q s) (ha : Cleared s a memory (lanes * q))
    (hb : Setup a b memory lanes q) : LoopReady memory lanes q b := by
  have ready := ha.ready hs
  refine ⟨ready.space.same hb.wr (hb.other .x19 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb.other .x24 (by decide) (by decide) (by decide) (by decide) (by decide))
    hb.sp, ?_,
    hb.destination, hb.lane, hb.remaining, hb.stride⟩
  rw [hb.mem, ha.mem]
  exact initialized_zero s.mem memory lanes q hs.space.bound _

theorem lanesSetup_rel : RelCT isa AgreeBases lanesSetupCode (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs publicBases)
    (fun _ _ h => h.taint) (by taint_decide)

theorem Setup.agree {s t a b : State} {memory : Addr} {lanes q : Nat}
    (ha : Setup s a memory lanes q) (hb : Setup t b memory lanes q)
    (hp : AgreeBases s t) : AgreeSaved a b := by
  refine ⟨ha.sp.trans (hp.1.trans hb.sp.symm), ?_⟩
  intro r hr
  by_cases h14 : r = .x22
  · subst r; exact ha.destination.trans hb.destination.symm
  by_cases h12 : r = .x20
  · subst r; exact ha.lane.trans hb.lane.symm
  by_cases h15 : r = .x23
  · subst r; exact ha.remaining.trans hb.remaining.symm
  by_cases h13 : r = .x21
  · subst r; exact ha.stride.trans hb.stride.symm
  have included : ∀ r ∈ savedRegs, r ≠ .x22 → r ≠ .x20 → r ≠ .x23 → r ≠ .x21 →
      r ∈ publicBases := by decide
  exact (ha.other r h14 h12 h15 h13 ((show ∀ r ∈ savedRegs, r ≠ .x15 from by decide) r hr)).trans
    ((hp.2 r (included r hr h14 h12 h15 h13)).trans (hb.other r h14 h12 h15 h13 ((show ∀ r ∈ savedRegs, r ≠ .x15 from by decide) r hr)).symm)

theorem lanesLoop_ready_rel (v : HPrime.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    RelCT isa (fun s t => LoopReady memory lanes q s ∧ LoopReady memory lanes q t ∧
      AgreeSaved s t) (.loop (lane name v.hash) (.nonzero .x .x15)) AgreeSaved := by
  intro s t ts tt a b hp es et
  have initial {s : State} (h : LoopReady memory lanes q s) :
      LoopI s memory lanes q 0 (bytesAt s.mem (s.gpr .x19) 64) s :=
    ⟨by omega, by simpa using h.destination, h.lane,
      by simpa only [Nat.sub_zero] using h.remaining, h.stride, Keeps.refl _ _ _,
      h.initialized, rfl⟩
  exact lanesLoop_rel v name s t memory lanes q _ _ hp.1.space hp.2.1.space lo
    lanesBound hq _ _ _ _ _ _ ⟨initial hp.1, initial hp.2.1, hp.2.2⟩ es et

theorem code_ct (v : HPrime.Backend) (name : String)
    (memory : Addr) (lanes q : Nat) (lo : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64)
    (hq : 2 ≤ q) :
    ConstantTime isa (Ready memory lanes q) AgreeBases (code name v.hash) := by
  let P := fun s t => Ready memory lanes q s ∧ Ready memory lanes q t ∧ AgreeBases s t
  have blocksPositive : 1 ≤ lanes * q := by
    have mul := Nat.mul_le_mul_right q lo
    rw [Nat.one_mul] at mul; omega
  have cleared := (clear_rel memory lanes q).wpDep (fun s t hp =>
    ⟨clear_ok s memory (lanes * q) blocksPositive hp.1.space.bound hp.1.memoryRead
        hp.1.blocksRead hp.1.memoryWord hp.1.blocksWord hp.1.space.matrix,
      clear_ok t memory (lanes * q) blocksPositive hp.2.1.space.bound hp.2.1.memoryRead
        hp.2.1.blocksRead hp.2.1.memoryWord hp.2.1.blocksWord hp.2.1.space.matrix⟩)
  let R := fun a b => AgreeBases a b ∧ ∃ s t, P s t ∧
    Cleared s a memory (lanes * q) ∧ Cleared t b memory (lanes * q)
  have setup := (lanesSetup_rel.mono (P' := R) (fun _ _ h => h.1)
    (fun _ _ h => h)).wpDep (F := fun a b => Setup a b memory lanes q) (by
    intro a b hp
    obtain ⟨_, s, t, hst, ha, hb⟩ := hp
    have ra := ha.ready hst.1
    have rb := hb.ready hst.2.1
    exact ⟨lanesSetup_ok a memory lanes q ra.memoryRead ra.lanesRead ra.memoryWord
        ra.lanesWord ra.laneLength,
      lanesSetup_ok b memory lanes q rb.memoryRead rb.lanesRead rb.memoryWord
        rb.lanesWord rb.laneLength⟩)
  have prepared : RelCT isa R lanesSetupCode (fun a b =>
      LoopReady memory lanes q a ∧ LoopReady memory lanes q b ∧ AgreeSaved a b) := setup.mono (fun _ _ h => h) (by
    intro a b h
    obtain ⟨_, c, d, hp, ha, hb⟩ := h
    obtain ⟨pub, s, t, hst, hc, hd⟩ := hp
    exact ⟨ha.loopReady hst.1 hc, hb.loopReady hst.2.1 hd, ha.agree hb pub⟩)
  exact (cleared.seq (prepared.seq (lanesLoop_ready_rel v name memory lanes q lo
    lanesBound hq))).constantTime

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Initialization retains its byte stride and every public frame word outside its lane suffix. -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  initialized : Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .x19) 64)
  bp : t.gpr .x19 = s.gpr .x19
  bx : t.gpr .x24 = s.gpr .x24
  sp : t.sp = s.sp
  stride : t.gpr .x21 = BitVec.ofNat 64 (1024 * q)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem complete_ok (v : HPrime.Backend) (name : String) (s : State)
    (memory : Addr) (lanes q : Nat) (ready : Ready memory lanes q s)
    (positive : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (minimum : 2 ≤ q) :
    WP isa (Impl.Argon2.AArch64.MemoryInit.code name v.hash) s (Done s · memory lanes q) :=
  (code_ok v name s memory lanes q positive minimum lanesBound ready.space ready.memoryRead ready.lanesRead
    ready.blocksRead ready.memoryWord ready.lanesWord ready.blocksWord ready.laneLength).mono
      (fun _ ⟨initialized, bp, bx, sp, stride, rd, wr, frame, unused⟩ =>
        ⟨initialized, bp, bx, sp, stride, rd, wr, frame, unused⟩)

theorem Done.frame_word {s t : State} {memory : Addr} {lanes q : Nat}
    (space : Space s memory (1024 * (lanes * q))) (done : Done s t memory lanes q)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 64 ∨ 72 ≤ d) :
    t.mem.readW (t.gpr .x19 + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .x19 + BitVec.ofNat 64 d) 64 := by
  rw [done.bp]
  have sub : Region.Sub ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .x19, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨s.gpr .x19 + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact space.frameMatrix.sub_left sub
    · exact space.frameWork.sub_left sub
    · exact space.stackFrame.symm.sub_left sub
    · exact Offset.disjoint (s.gpr .x19) separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.MemoryInit
end

/-! Merged from `Proof.Argon2.AArch64.InitFillReady`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSetupReset`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSetupDimensions`. -/
section
/-! Initialization's byte stride gives exact block and segment counts without division instructions. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

theorem dimensions_ok (s : State) : WP isa (.block Impl.Argon2.AArch64.FillSetup.dimensions) s fun t =>
    t.gpr .x20 = s.gpr .x21 >>> 10 ∧ t.gpr .x21 = s.gpr .x21 >>> 12 ∧ Divide.Keeps [.x20, .x21, .x15] s t := by
  apply WP.of_runBlock
  simp only [Impl.Argon2.AArch64.FillSetup.dimensions,
    Impl.Argon2.AArch64.Instructions.mov, Impl.Argon2.AArch64.Instructions.shr,
    Impl.Argon2.AArch64.Instructions.mark,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    show 0 < 4096 from by decide, show (10 : Nat) < 64 from by decide,
    show (12 : Nat) < 64 from by decide, BitVec.setWidth_eq, BitVec.add_zero,
    RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem stride_shift (q shift : Nat) (bound : 1024 * q < 2 ^ 64) :
    BitVec.ofNat 64 (1024 * q) >>> shift = BitVec.ofNat 64 ((1024 * q) / 2 ^ shift) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) bound)]

theorem dimensions_nat_ok (s : State) (p : Params) (bound : 1024 * p.laneLen < 2 ^ 64)
    (stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * p.laneLen)) :
    WP isa (.block Impl.Argon2.AArch64.FillSetup.dimensions) s fun t =>
      t.gpr .x20 = BitVec.ofNat 64 p.laneLen ∧ t.gpr .x21 = BitVec.ofNat 64 p.segmentLen ∧
      Divide.Keeps [.x20, .x21, .x15] s t := by
  refine (dimensions_ok s).mono ?_
  rintro t ⟨lane, segment, keeps⟩
  refine ⟨?_, ?_, keeps⟩
  · rw [lane, stride, stride_shift _ 10 bound]
    simp only [show 2 ^ 10 = 1024 from rfl, Nat.mul_div_cancel_left _ (by decide : 0 < 1024)]
  · rw [segment, stride, stride_shift _ 12 bound]
    have div : 1024 * p.laneLen / 4096 = p.laneLen / 4 := by
      rw [show (4096 : Nat) = 1024 * 4 from rfl, Nat.mul_div_mul_left _ _ (by decide : 0 < 1024)]
    rw [show 2 ^ 12 = 4096 from rfl, div]
    rfl

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Reset public loop coordinates and only the pass word in the enclosing frame. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Reset (s t : State) : Prop where
  mem : t.mem = s.mem.writeW (off (s.gpr .x19) 0) (0 : Addr)
  lane : t.gpr .x24 = 0
  slice : t.gpr .x22 = 0
  regs : ∀ r, r ∉ [Reg.x8, .x24, .x22] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem reset_ok (s : State) (write : InRegions s.wr (off (s.gpr .x19) 0) 8) :
    WP isa (.block Impl.Argon2.AArch64.FillSetup.reset) s (Reset s) := by
  apply WP.of_runBlock
  simp only [off, BitVec.add_zero] at write
  simp only [Impl.Argon2.AArch64.FillSetup.reset,
    Impl.Argon2.AArch64.Instructions.imm, Impl.Argon2.AArch64.Instructions.store,
    show 0 < 65536 from by decide, List.flatten_cons, List.flatten_nil,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, Size.bytes, Size.bits, State.store, State.read,
    show 0 % 8 = 0 ∧ 0 < 4096 * 8 from by decide, and_self,
    Nat.reduceMul, Nat.reduceLT,
    BitVec.shiftLeft_zero, show (0#16).setWidth 64 = 0#64 from rfl,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    BitVec.add_zero, BitVec.setWidth_eq, write, reduceCtorEq, ite_true, ite_false,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  constructor
  · simp only [RegUpd.mem_write, off, BitVec.add_zero, Mem.writeW]; rfl
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
    rfl
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  · simp only [RegUpd.rd_write]
  · simp only [RegUpd.wr_write]
  · simp only [RegUpd.sp_write]

theorem Reset.pass {s t : State} (h : Reset s t) : t.mem.readW (off (t.gpr .x19) 0) 64 = 0 := by
  rw [h.mem, h.regs .x19 (by decide)]
  exact Mem.readW_writeW_self64 _ _ _

theorem Reset.frame {s t : State} (h : Reset s t) : Frame [⟨s.gpr .x19, 8⟩] s.mem t.mem := by
  rw [h.mem]
  exact (Frame.refl _ _).writeW (r := ⟨s.gpr .x19, 8⟩) (by simp) _
    (by simpa only [off, BitVec.add_zero] using Region.contains_self (s.gpr .x19) 8)

theorem Reset.read {s t : State} (h : Reset s t) (d : Nat) (separate : 8 ≤ d) (bound : d + 8 ≤ 272) :
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
  rw [h.mem, h.regs .x19 (by decide)]
  exact Mem.readW_writeW_sep (w := 64) (w' := 64)
    (Offset.sep _ (d := d) (n := 8) (e := 0) (k := 8) (Or.inr (by omega)) (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Merged from `Proof.Argon2.AArch64.FillSetupFinish`. -/
section
/-! Merged from `Proof.Argon2.AArch64.FillSetupEnvironment`. -/
section
/-! Initialization hands filling the reviewed dimensions and stable public frame words. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Environment (p : Params) (s : State) : Prop where
  parameters : FillContext.Parameters p 0 0 0
  passesBound : p.passes < 2 ^ 32
  layout : FillKernel.Layout p s
  addressLayout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .x19) d) 8
  counterWrite : InRegions s.wr (off (s.gpr .x19) 8) 8
  passWrite : InRegions s.wr (off (s.gpr .x19) 0) 8
  matrixWork : (⟨FillKernel.matrix s, p.blocks * 1024⟩ : Region).Disjoint ⟨AddressCalls.work s, 8192⟩
  blocksWord : s.mem.readW (off (s.gpr .x19) 240) 64 = BitVec.ofNat 64 p.blocks
  passesWord : s.mem.readW (off (s.gpr .x19) 72) 64 = BitVec.ofNat 64 p.passes
  variantWord : s.mem.readW (off (s.gpr .x19) 112) 64 = BitVec.ofNat 64 p.variant.code
  lanesWord : s.mem.readW (off (s.gpr .x19) 184) 64 = BitVec.ofNat 64 p.lanes

theorem Environment.of_state {p : Params} {s t : State} (h : Environment p s)
    (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) : Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := by unfold FillKernel.matrix; rw [mem, bp]
  have work : AddressCalls.work t = AddressCalls.work s := by unfold AddressCalls.work; rw [mem, bp]
  refine ⟨h.parameters, h.passesBound, h.layout.of_preserved bp sp base work rd wr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.addressLayout.frameRead
    · rw [wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.counterWrite
  · rw [wr, bp]; exact h.passWrite
  · rw [base, work]; exact h.matrixWork
  all_goals rw [mem, bp]
  · exact h.blocksWord
  · exact h.passesWord
  · exact h.variantWord
  · exact h.lanesWord

theorem Reset.header {p : Params} {s t : State} (h : Environment p s) (reset : Reset s t)
    (laneLength : t.gpr .x20 = BitVec.ofNat 64 p.laneLen)
    (segmentLength : t.gpr .x21 = BitVec.ofNat 64 p.segmentLen) : FillHeader.Ready p 0 0 0 t := by
  have bp := reset.regs .x19 (by decide)
  have sp := reset.sp
  have base : FillKernel.matrix t = FillKernel.matrix s := reset.read 232 (by decide) (by decide)
  have work : AddressCalls.work t = AddressCalls.work s := reset.read 248 (by decide) (by decide)
  refine ⟨h.layout.of_preserved bp sp base work reset.rd reset.wr, ?_, ?_, ?_, ?_, ?_, laneLength,
    segmentLength, (reset.read 184 (by decide) (by decide)).trans h.lanesWord⟩
  · constructor
    · rw [reset.rd, reset.wr, bp]; exact h.addressLayout.frameRead
    · rw [reset.wr, work]; exact h.addressLayout.workWrite
    · rw [bp, work]; exact h.addressLayout.frameWork
    · rw [bp, sp]; exact h.addressLayout.frameStack
    · rw [sp, work]; exact h.addressLayout.stackWork
  · rw [reset.rd, reset.wr, bp]; exact h.reads
  · rw [reset.wr, bp]; exact h.counterWrite
  · refine ⟨(s.mem.readW (off (s.gpr .x19) 8) 64).toNat, reset.pass, reset.lane, reset.slice,
      (reset.read 240 (by decide) (by decide)).trans h.blocksWord,
      (reset.read 72 (by decide) (by decide)).trans h.passesWord,
      (reset.read 112 (by decide) (by decide)).trans h.variantWord, ?_⟩
    rw [reset.read 8 (by decide) (by decide)]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [base, work]; exact h.matrixWork

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Merged from `Proof.Argon2.AArch64.FillSetup`. -/
section
/-! Establish the complete pass-loop invariant from memory initialization's byte stride. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  environment : Environment p s
  bound : 1024 * p.laneLen < 2 ^ 64
  stride : s.gpr .x21 = BitVec.ofNat 64 (1024 * p.laneLen)

structure Prepared (s t : State) (p : Params) : Prop where
  ready : FillIterations.Ready p 0 t
  matrix : FillKernel.matrix t = FillKernel.matrix s
  work : AddressCalls.work t = AddressCalls.work s
  regs : ∀ r ∈ FillCompress.loopRegs, r ≠ .x24 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x19, 8⟩] s.mem t.mem
  sp : t.sp = s.sp
  words : ∀ d, 8 ≤ d → d + 8 ≤ 272 →
    t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64

theorem code_ok (s : State) (p : Params) (h : Ready p s) :
    WP isa Impl.Argon2.AArch64.FillSetup.code s (Prepared s · p) := by
  unfold Impl.Argon2.AArch64.FillSetup.code
  refine WP.seq ((dimensions_nat_ok s p h.bound h.stride).mono ?_)
  rintro a ⟨laneLength, segmentLength, keeps⟩
  have bp := keeps.regs .x19 (by decide)
  have sp := keeps.sp
  have environment := h.environment.of_state bp sp keeps.mem keeps.rd keeps.wr
  refine (reset_ok a environment.passWrite).mono ?_
  intro t reset
  have header := reset.header environment ((reset.regs .x20 (by decide)).trans laneLength)
    ((reset.regs .x21 (by decide)).trans segmentLength)
  have words (d : Nat) (lower : 8 ≤ d) (upper : d + 8 ≤ 272) :
      t.mem.readW (off (t.gpr .x19) d) 64 = s.mem.readW (off (s.gpr .x19) d) 64 := by
    rw [reset.read d lower upper, keeps.mem, bp]
  refine ⟨⟨⟨environment.parameters, 0, 0, header⟩, environment.passesBound, ?_⟩,
    words 232 (by decide) (by decide), words 248 (by decide) (by decide), ?_,
    reset.rd.trans keeps.rd, reset.wr.trans keeps.wr, ?_, reset.sp.trans keeps.sp, words⟩
  · rw [reset.wr, reset.regs .x19 (by decide)]; exact environment.passWrite
  · intro r hr bx q g sl
    have ne : r ≠ .x8 ∧ r ≠ .x15 := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (reset.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨ne.1, bx, sl⟩)).trans
      (keeps.regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact ⟨q, g, ne.2⟩))
  · have frame := reset.frame
    rw [bp, keeps.mem] at frame; exact frame

theorem Prepared.represents {s t : State} {p : Params} (ready : Ready p s) (done : Prepared s t p)
    (blocks : Array Block) (represented : Proof.Argon2.Represents s.mem (FillKernel.matrix s) p.blocks blocks) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks blocks := by
  rw [done.matrix]
  refine ⟨represented.size, ?_⟩
  intro k hk
  apply Eq.trans _ (represented.block k hk)
  apply FillCompress.block_frame done.frame
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact (ready.environment.layout.matrixFrame.sub_left (Proof.Argon2.matrixCell_sub _ _ _ hk)).sub_right
    (Region.sub_prefix (by decide))

theorem code_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    Impl.Argon2.AArch64.FillSetup.code (fun _ _ => True) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr; simp only [Taint.mem_ofRegs, List.mem_singleton] at hr; subst r; exact h.1⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ _ => trivial)

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Filling setup retains the final-call layout and establishes the reduction dimensions. -/

namespace VG.Proof.Argon2.AArch64.FillSetup

open VG VG.AArch64 VG.Spec.Argon2

theorem Prepared.finish_ready {s t : State} {p : Params} (ready : Ready p s) (done : Prepared s t p)
    (outputReady : FinalOutput.Ready p s) (positive : 0 < p.passes) : FillFinish.Ready p t := by
  have bp := done.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)
  have sp := done.sp
  have base : ReductionState.matrix t = ReductionState.matrix s := done.matrix
  have output : FinalOutput.output t = FinalOutput.output s := done.words 256 (by decide) (by decide)
  have work : FinalOutput.work t = FinalOutput.work s := done.words 248 (by decide) (by decide)
  obtain ⟨lane, slice, header⟩ := done.ready.filling.header
  have params := ready.environment.parameters
  refine ⟨done.ready, ⟨?_, ?_⟩, positive⟩
  · refine ⟨⟨params.lanesPositive, params.segment_bound.1, ?_, header.layout.frameRead 232 (by simp),
      header.layout.matrixWrite, header.layout.matrixFrame, header.laneLength⟩,
      params.lanesBound, header.layout.frameRead 184 (by simp), header.lanesWord⟩
    have blocks := Proof.Argon2.blocks_le_memory p
    have memory := params.memoryBound
    omega
  · refine ⟨?_, outputReady.positive, outputReady.bound, ?_,
      (done.words 264 (by decide) (by decide)).trans outputReady.tagWord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sp]; exact outputReady.stackMinimum
    · rw [done.rd, done.wr, bp]; exact outputReady.reads
    · rw [base, done.rd, done.wr]; exact outputReady.input
    · rw [output, done.wr]; exact outputReady.outputWrite
    · rw [work, done.wr]; exact outputReady.workWrite
    · rw [base, work]; exact outputReady.inputWork
    · rw [output, work]; exact outputReady.outputWork
    · rw [sp, base]; exact outputReady.stackInput
    · rw [sp, output]; exact outputReady.stackOutput
    · rw [sp, work]; exact outputReady.stackWork

end VG.Proof.Argon2.AArch64.FillSetup
end

/-! Retain the filling environment and final-call layout across memory initialization. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2

structure Ready (p : Params) (s : State) : Prop where
  initializing : MemoryInit.Ready (FillKernel.matrix s) p.lanes p.laneLen s
  environment : FillSetup.Environment p s
  output : FinalOutput.Ready p s
  positive : 0 < p.passes
  scratch : s.gpr .x24 = FinalOutput.work s

theorem initialized_environment {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Environment p t := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have work : AddressCalls.work t = AddressCalls.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have e := h.environment
  refine ⟨e.parameters, e.passesBound, e.layout.of_preserved done.bp done.sp base work done.rd done.wr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rw [done.rd, done.wr, done.bp]; exact e.addressLayout.frameRead
    · rw [done.wr, work]; exact e.addressLayout.workWrite
    · rw [done.bp, work]; exact e.addressLayout.frameWork
    · rw [done.bp, done.sp]; exact e.addressLayout.frameStack
    · rw [done.sp, work]; exact e.addressLayout.stackWork
  · rw [done.rd, done.wr, done.bp]; exact e.reads
  · rw [done.wr, done.bp]; exact e.counterWrite
  · rw [done.wr, done.bp]; exact e.passWrite
  · rw [base, work]; exact e.matrixWork
  · exact (done.frame_word h.initializing.space 240 (by decide) (Or.inr (by decide))).trans e.blocksWord
  · exact (done.frame_word h.initializing.space 72 (by decide) (Or.inr (by decide))).trans e.passesWord
  · exact (done.frame_word h.initializing.space 112 (by decide) (Or.inr (by decide))).trans e.variantWord
  · exact (done.frame_word h.initializing.space 184 (by decide) (Or.inr (by decide))).trans e.lanesWord

theorem initialized_output {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FinalOutput.Ready p t := by
  have base : ReductionState.matrix t = ReductionState.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have output : FinalOutput.output t = FinalOutput.output s := done.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have work : FinalOutput.work t = FinalOutput.work s := done.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  refine ⟨(by rw [done.sp]; exact h.output.stackMinimum), h.output.positive, h.output.bound, ?_,
    (done.frame_word h.initializing.space 264 (by decide) (Or.inr (by decide))).trans h.output.tagWord,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [done.rd, done.wr, done.bp]; exact h.output.reads
  · rw [base, done.rd, done.wr]; exact h.output.input
  · rw [output, done.wr]; exact h.output.outputWrite
  · rw [work, done.wr]; exact h.output.workWrite
  · rw [base, work]; exact h.output.inputWork
  · rw [output, work]; exact h.output.outputWork
  · rw [done.sp, base]; exact h.output.stackInput
  · rw [done.sp, output]; exact h.output.stackOutput
  · rw [done.sp, work]; exact h.output.stackWork

theorem initialized_setup {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : FillSetup.Ready p t := by
  have params := h.environment.parameters
  have product : p.laneLen ≤ p.lanes * p.laneLen := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right p.laneLen (show 1 ≤ p.lanes from params.lanesPositive)
  refine ⟨initialized_environment h done, ?_, done.stride⟩
  have bound := h.initializing.space.bound
  have bytes := Nat.mul_le_mul_left 1024 product
  omega

theorem initialized_represents {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) :
    Proof.Argon2.Represents t.mem (FillKernel.matrix t) p.blocks
      (initMemory p (Spec.Blake2.bytesAt s.mem (s.gpr .x19) 64)).memory := by
  have base : FillKernel.matrix t = FillKernel.matrix s := done.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  rw [base]
  have segments := Proof.Argon2.laneLen_segments p h.environment.parameters.lanesPositive
  have minimum := h.environment.parameters.segment_bound.1
  exact done.initialized.represents h.environment.parameters.lanesPositive (by omega)

end VG.Proof.Argon2.AArch64.InitFill
end

/-! Merged from `Proof.Argon2.AArch64.InitFillFrames`. -/
section
/-! Each stage writes only the matrix, hash scratch, output, call stack and local hash prefix. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2

def writes (s : State) (p : Params) : List Region :=
  [⟨FillKernel.matrix s, p.blocks * 1024⟩, ⟨FinalOutput.work s, 16384⟩,
    ⟨FinalOutput.output s, p.tagLen⟩, below (s.sp) 16, ⟨s.gpr .x19, 72⟩]

theorem initialization_frame {s t : State} {p : Params} (h : Ready p s)
    (done : MemoryInit.Done s t (FillKernel.matrix s) p.lanes p.laneLen) : Frame (writes s p) s.mem t.mem := by
  apply done.frame.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · have blocks := Proof.Argon2.blocks_lanes p h.environment.parameters.lanesPositive
    exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [writes], by rw [blocks, Nat.mul_comm 1024]; intro _ h; exact h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [writes], by rw [h.scratch]; intro _ h; exact h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨s.gpr .x19, 72⟩, by simp [writes], Offset.sub_base _ (by decide)⟩

theorem setup_frame {s t : State} {p : Params} (h : Frame [⟨s.gpr .x19, 8⟩] s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact ⟨⟨s.gpr .x19, 72⟩, by simp [writes], Region.sub_prefix (by decide)⟩

theorem filling_frame {s t : State} {p : Params} (positive : 0 < p.blocks) (h : Frame (FillFinish.writes s p) s.mem t.mem) :
    Frame (writes s p) s.mem t.mem := by
  apply h.sub
  intro r hr
  simp only [FillFinish.writes, FillIterations.writes, Finish.writes,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl | rfl)
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨⟨FinalOutput.work s, 16384⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨below (s.sp) 16, by simp [writes], below_sub (by decide) (by decide)⟩
  · exact ⟨⟨s.gpr .x19, 72⟩, by simp [writes], Region.sub_prefix (by decide)⟩
  · exact ⟨⟨FillKernel.matrix s, p.blocks * 1024⟩, by simp [writes], Region.sub_prefix (by omega)⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩
  · exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.AArch64.InitFill
end

/-! Exact initialization, every filling pass, final reduction and H′ after the reviewed H₀. -/

namespace VG.Proof.Argon2.AArch64.InitFill

open VG VG.AArch64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

def result (p : Params) (h0 : List Byte) : List Byte :=
  Spec.Argon2.finish p (Proof.Argon2.iterations p 0 p.passes (initMemory p h0)).memory

structure Done (s t : State) (p : Params) : Prop where
  digest : bytesAt t.mem (FinalOutput.output s) p.tagLen = result p (bytesAt s.mem (s.gpr .x19) 64)
  bp : t.gpr .x19 = s.gpr .x19
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p) s.mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem writes_eq (s t : State) (p : Params) (bp : t.gpr .x19 = s.gpr .x19) (sp : t.sp = s.sp)
    (base : FillKernel.matrix t = FillKernel.matrix s) (work : FinalOutput.work t = FinalOutput.work s)
    (output : FinalOutput.output t = FinalOutput.output s) : writes t p = writes s p := by
  unfold writes
  rw [bp, sp, base, work, output]

theorem code_ok (v : HPrime.Backend) (name : String) (s : State) (p : Params) (h : Ready p s) :
    WP isa (Impl.Argon2.AArch64.InitFill.code name v.hash) s (Done s · p) := by
  have params := h.environment.parameters
  have q : 2 ≤ p.laneLen := by
    have segments := Proof.Argon2.laneLen_segments p params.lanesPositive
    have minimum := params.segment_bound.1
    omega
  have blocks := Proof.Argon2.lastIndex_bounds p params.lanesPositive params.segment_bound.1 0 params.lanesPositive
  unfold Impl.Argon2.AArch64.InitFill.code
  refine WP.seq ((MemoryInit.complete_ok v name s (FillKernel.matrix s) p.lanes p.laneLen h.initializing
    params.lanesPositive (Nat.lt_trans params.lanesBound (by decide)) q).mono ?_)
  intro a initialized
  have setupReady := initialized_setup h initialized
  have initializedBase : FillKernel.matrix a = FillKernel.matrix s :=
    initialized.frame_word h.initializing.space 232 (by decide) (Or.inr (by decide))
  have initializedWork : FinalOutput.work a = FinalOutput.work s :=
    initialized.frame_word h.initializing.space 248 (by decide) (Or.inr (by decide))
  have initializedOutput : FinalOutput.output a = FinalOutput.output s :=
    initialized.frame_word h.initializing.space 256 (by decide) (Or.inr (by decide))
  have rep : Proof.Argon2.Represents a.mem (FillKernel.matrix a) p.blocks
      (initMemory p (bytesAt s.mem (s.gpr .x19) 64)).memory := by
    rw [initializedBase]
    exact initialized.initialized.represents params.lanesPositive (by omega)
  refine WP.seq ((FillSetup.code_ok a p setupReady).mono ?_)
  intro b prepared
  refine (FillFinish.code_ok v name b p (prepared.finish_ready setupReady (initialized_output h initialized) h.positive)
    (initMemory p (bytesAt s.mem (s.gpr .x19) 64)) (prepared.represents setupReady _ rep)).mono ?_
  intro t filled
  have bp := prepared.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide) (by decide)
  have sp := prepared.sp
  have work : FinalOutput.work b = FinalOutput.work a := prepared.words 248 (by decide) (by decide)
  have output : FinalOutput.output b = FinalOutput.output a := prepared.words 256 (by decide) (by decide)
  refine ⟨?_, (filled.regs .x19 (by simp [FillCompress.loopRegs]) (by decide) (by decide) (by decide)).trans (bp.trans initialized.bp),
    filled.sp.trans (sp.trans initialized.sp),
    filled.rd.trans (prepared.rd.trans initialized.rd), filled.wr.trans (prepared.wr.trans initialized.wr), ?_, ?_⟩
  · have digest := filled.digest
    rw [output, initializedOutput] at digest
    exact digest
  · have initialFrame := initialization_frame h initialized
    have setupFrame := setup_frame (p := p) prepared.frame
    rw [writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at setupFrame
    have fillFrame := filling_frame (by omega : 0 < p.blocks) filled.frame
    rw [writes_eq a b p bp sp prepared.matrix work output,
      writes_eq s a p initialized.bp initialized.sp initializedBase initializedWork initializedOutput] at fillFrame
    exact (initialFrame.trans setupFrame).trans fillFrame
  · intro r hr
    have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
        r ∈ FillCompress.loopRegs ∧ r ≠ .x24 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x20 ∧ r ≠ .x21 := by decide
    obtain ⟨member, h24, h22, h23, h20, h21⟩ := facts r hr
    exact (filled.regs r member h24 h22 h23).trans
      ((prepared.regs r member h24 h20 h21 h22).trans (initialized.unused r hr))

theorem result_derive (p : Params) (password salt secret ad : List Byte) :
    result p (initialHash p password salt secret ad) = derive p password salt secret ad := by
  unfold result derive
  rw [Proof.Argon2.iterations_fill]

end VG.Proof.Argon2.AArch64.InitFill
