import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Written

/-! # H′: permissions and separation at an output cursor -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_mov)
open VG.Spec.Blake2 (bytesAt)

structure Space (s : State) (n : Nat) : Prop where
  bound : n < 2 ^ 32
  spBound : 16 ≤ s.sp.toNat
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  out : ∀ i < n, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1
  sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, n⟩
  stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩
  stackOut : (below s.sp 16).Disjoint ⟨s.gpr .x22, n⟩

theorem Space.advance {s t : State} {xs : List Byte} {n k : Nat}
    (h : Space s n) (written : Written s xs t) (size : xs.length + k ≤ n) : Space t k := by
  have suffix : Region.Sub ⟨t.gpr .x22, k⟩ ⟨s.gpr .x22, n⟩ := by
    rw [written.output]; exact Offset.sub_base _ size
  refine ⟨by have := h.bound; omega, by rw [written.sp]; exact h.spBound, ?_, ?_, ?_, ?_, ?_⟩
  · rw [written.wr, written.x24]; exact h.work
  · intro i hi
    rw [written.wr, written.output, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.out (xs.length + i) (by omega)
  · rw [written.x24]; exact h.sep.sub_right suffix
  · rw [written.x24, written.sp]; exact h.stackWork
  · rw [written.sp]; exact h.stackOut.sub_right suffix

theorem Space.keeps {s t : State} {n : Nat} (h : Space s n) (k : Keeps s t) : Space t n :=
  h.advance (Written.of_keeps k) (by simp only [List.length_nil, Nat.zero_add, Nat.le_refl])

theorem Space.prefix {s : State} {n k : Nat} (h : Space s n) (hk : k ≤ n) : Space s k := by
  refine ⟨by have := h.bound; omega, h.spBound, h.work, fun i hi => h.out i (by omega),
    h.sep.sub_right (Region.sub_prefix hk), h.stackWork, h.stackOut.sub_right (Region.sub_prefix hk)⟩

theorem Space.join {s u t : State} {xs ys : List Byte} {n : Nat} (h : Space s n)
    (first : Written s xs u) (last : Written u ys t) (size : xs.length + ys.length ≤ n) :
    Written s (xs ++ ys) t :=
  first.trans last (by have := h.bound; omega)
    (h.sep.sub_right (Region.sub_prefix size)) (h.stackOut.sub_right (Region.sub_prefix size))

theorem copyRemaining_ok (s : State) (n : Nat) (space : Space s n)
    (lo : 1 ≤ n) (hi : n ≤ 64) (count : s.gpr .x23 = BitVec.ofNat 64 n) :
    WP isa copyRemaining s fun t => Written s (bytesAt s.mem (s.gpr .x24 + 768) n) t := by
  unfold copyRemaining
  refine WP.seq (wp_mov fun a ha => WP.block_nil ?_)
  have base := ha.other .x24 (by decide)
  have dst := ha.other .x22 (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [base, ha.wr]; exact space.work
  have outA : ∀ i < n, InRegions a.wr (a.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [dst, ha.wr]; exact space.out
  have sepA : (⟨a.gpr .x24 + 768, n⟩ : Region).Disjoint ⟨a.gpr .x22, n⟩ := by
    rw [base, dst]; exact space.sep.sub_left (Offset.sub_base _ (by omega : 768 + n ≤ 16384))
  refine (copy_ok a n lo hi (ha.gpr.trans count) workA outA sepA).mono ?_
  intro t ht
  have result := Written.of_copied ht (by have := space.bound; omega)
  refine ⟨?_, fun r hr h30 h1 h2 => ?_, result.rd.trans ha.rd, result.wr.trans ha.wr, result.sp.trans ha.sp, ?_, ?_⟩
  · simpa only [dst, ha.mem, base] using result.output
  · have hrax : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (result.regs r hr h30 h1 h2).trans (ha.other r hrax)
  · simpa only [base, dst, ha.mem, ha.sp] using result.frame
  · simpa only [base, dst, ha.mem] using result.bytes

end VG.Proof.Argon2.AArch64.HPrime
