import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitStage

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
