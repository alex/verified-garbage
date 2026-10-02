import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitCT
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitRepresent

/-! Initialization retains its byte stride and every public frame word outside its lane suffix. -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64 VG.Spec.Argon2
open VG.Spec.Blake2 (bytesAt)

structure Done (s t : State) (memory : Addr) (lanes q : Nat) : Prop where
  initialized : Initialized t.mem memory lanes q lanes (bytesAt s.mem (s.gpr .rbp) 64)
  bp : t.gpr .rbp = s.gpr .rbp
  bx : t.gpr .rbx = s.gpr .rbx
  sp : t.gpr .rsp = s.gpr .rsp
  stride : t.gpr .r13 = BitVec.ofNat 64 (1024 * q)
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨memory, 1024 * (lanes * q)⟩, ⟨s.gpr .rbx, 16384⟩,
    below (s.gpr .rsp) 24, ⟨s.gpr .rbp + 64, 8⟩] s.mem t.mem

theorem complete_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (memory : Addr) (lanes q : Nat) (ready : Ready memory lanes q s)
    (positive : 1 ≤ lanes) (lanesBound : lanes < 2 ^ 64) (minimum : 2 ≤ q) :
    WP isa (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)) s (Done s · memory lanes q) :=
  (code_ok v name s memory lanes q positive minimum lanesBound ready.space ready.memoryRead ready.lanesRead
    ready.blocksRead ready.memoryWord ready.lanesWord ready.blocksWord ready.laneLength).mono
      (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩)

theorem Done.frame_word {s t : State} {memory : Addr} {lanes q : Nat}
    (space : Space s memory (1024 * (lanes * q))) (done : Done s t memory lanes q)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 64 ∨ 72 ≤ d) :
    t.mem.readW (t.gpr .rbp + BitVec.ofNat 64 d) 64 = s.mem.readW (s.gpr .rbp + BitVec.ofNat 64 d) 64 := by
  rw [done.bp]
  have sub : Region.Sub ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact done.frame.readW (r := ⟨s.gpr .rbp + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact space.frameMatrix.sub_left sub
    · exact space.frameWork.sub_left sub
    · exact space.stackFrame.symm.sub_left sub
    · exact Offset.disjoint (s.gpr .rbp) separate (by omega) (by decide)) (by decide)

end VG.Proof.Argon2.X86_64.MemoryInit
