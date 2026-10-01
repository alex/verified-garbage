import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitMatrix

/-! # Permissions for the matrix, derivation frame and hash scratch -/

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Space (s : State) (memory : Addr) (bytes : Nat) : Prop where
  matrix : Covers [⟨memory, bytes⟩] s.wr
  frame : Covers [⟨s.gpr .rbp, 72⟩] s.wr
  work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr
  frameMatrix : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨memory, bytes⟩
  frameWork : (⟨s.gpr .rbp, 272⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  matrixWork : (⟨memory, bytes⟩ : Region).Disjoint ⟨s.gpr .rbx, 16384⟩
  stackFrame : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbp, 272⟩
  stackMatrix : (below (s.gpr .rsp) 24).Disjoint ⟨memory, bytes⟩
  stackWork : (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rbx, 16384⟩
  bound : bytes < 2 ^ 64

theorem Space.same {s t : State} {memory : Addr} {bytes : Nat} (h : Space s memory bytes)
    (wr : t.wr = s.wr) (bp : t.gpr .rbp = s.gpr .rbp)
    (bx : t.gpr .rbx = s.gpr .rbx) (sp : t.gpr .rsp = s.gpr .rsp) : Space t memory bytes := by
  constructor
  · rw [wr]; exact h.matrix
  · rw [bp, wr]; exact h.frame
  · rw [bx, wr]; exact h.work
  · rw [bp]; exact h.frameMatrix
  · rw [bp, bx]; exact h.frameWork
  · rw [bx]; exact h.matrixWork
  · rw [sp, bp]; exact h.stackFrame
  · rw [sp]; exact h.stackMatrix
  · rw [sp, bx]; exact h.stackWork
  · exact h.bound

theorem Space.blockReady {s : State} {memory : Addr} {bytes d : Nat}
    (h : Space s memory bytes) (dst : s.gpr .r14 = memory + BitVec.ofNat 64 d)
    (bound : d + 1024 ≤ bytes) : BlockReady s := by
  have outputSub : Region.Sub ⟨s.gpr .r14, 1024⟩ ⟨memory, bytes⟩ := by
    rw [dst]; exact Offset.sub_base _ bound
  have outputCover : Covers [⟨s.gpr .r14, 1024⟩] s.wr := by
    have narrow : Covers [⟨s.gpr .r14, 1024⟩] [⟨memory, bytes⟩] := Covers.of_sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨_, List.mem_singleton_self _, d, dst, bound⟩)
    exact fun p n hp => h.matrix p n (narrow p n hp)
  exact ⟨h.frame, outputCover, h.work,
    h.frameWork.sub_left (Region.sub_prefix (by decide)),
    (h.frameMatrix.sub_left (Region.sub_prefix (by decide))).sub_right outputSub,
    h.matrixWork.sub_left outputSub,
    h.stackFrame.sub_right (Region.sub_prefix (by decide)),
    h.stackMatrix.sub_right outputSub, h.stackWork⟩

end VG.Proof.Argon2.X86_64.MemoryInit
