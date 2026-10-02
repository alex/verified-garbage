import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitCT
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitRepresent

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
