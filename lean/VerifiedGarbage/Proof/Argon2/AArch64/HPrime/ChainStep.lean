import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Compare
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Next
import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Output

/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.AArch64.HPrime

open VG VG.AArch64 VG.Impl.Argon2.AArch64.HPrime
open VG.Proof.MdStream.AArch64 (wp_movz)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .x22 = s.gpr .x22 + 32
  remaining : t.gpr .x23 = s.gpr .x23 - 32
  regs : ∀ r ∈ preserved, r ≠ .x30 → r ≠ .x22 → r ≠ .x23 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  frame : Frame [⟨s.gpr .x24, 832⟩, below s.sp 16, ⟨s.gpr .x22, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .x24 + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)
  bytes : bytesAt t.mem (s.gpr .x22) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64)).take 32
  comparison : t.gpr .x9 = if (s.gpr .x23 - 32).toNat < 65 then 1 else 0

theorem chainStep_ok (v : Backend) (s : State)
    (hsp : 16 ≤ s.sp.toNat)
    (remainingBound : 32 ≤ (s.gpr .x23).toNat ∧ (s.gpr .x23).toNat < 2 ^ 32)
    (work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .x22 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .x24, 16384⟩ : Region).Disjoint ⟨s.gpr .x22, 32⟩)
    (stackWork : (below s.sp 16).Disjoint ⟨s.gpr .x24, 16384⟩) :
    WP isa (.seq (.block [.movz .x .x1 64 0])
      (.seq (next v.hash) (.seq emitPrefix (.block [.subImm .x .x9 .x23 65, .lsr .x .x9 .x9 63]))))
      s (ChainStep s) := by
  refine WP.seq (wp_movz fun a ha => WP.block_nil ?_)
  have ka : Keeps s a := Keeps.of_upd ha (by decide)
  have workA : (⟨a.gpr .x24, 16384⟩ : Region) ∈ a.wr := by rw [ka.x24, ka.wr]; exact work
  have stackA : (below a.sp 16).Disjoint ⟨a.gpr .x24, 16384⟩ := by
    rw [ka.x24, ka.sp]; exact stackWork
  have lengthA : (a.gpr .x1).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) (by rw [ka.sp]; exact hsp) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .x22 = s.gpr .x22 := ksu.regs _ (by decide) (by decide)
  have digestU : bytesAt u.mem (s.gpr .x24 + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .x24 + 768) 64) := by
    simpa only [lengthA, ka.x24, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .x24, 16384⟩ : Region) ∈ u.wr := by rw [ksu.x24, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .x22 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .x24 + 768, 32⟩ : Region).Disjoint ⟨u.gpr .x22, 32⟩ := by
    rw [ksu.x24, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  have remainingW : (w.gpr .x23).toNat < 2 ^ 32 := by
    rw [hw.remaining, ksu.regs _ (by decide) (by decide),
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact remainingBound.1)]
    exact Nat.lt_of_le_of_lt (Nat.sub_le ..) remainingBound.2
  refine (compare_ok w remainingW).mono fun t compared => ?_
  have gt := compared.other
  have mt := compared.mem
  have rt := compared.rd
  have wt := compared.wr
  have fw : Frame [⟨s.gpr .x22, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h30 h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), compared.sp.trans (hw.sp.trans ksu.sp), ?_, ?_, ?_, ?_⟩
  · rw [gt _ (by decide), hw.output, dstU]
  · rw [gt _ (by decide), hw.remaining, ksu.regs _ (by decide) (by decide)]
  · have h9 : r ≠ .x9 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [gt r h9]
    have hrax : r ≠ .x8 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .x3 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .x2 := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr h30)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .x24 + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.x24, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [compared.value, hw.remaining, ksu.regs _ (by decide) (by decide)]

end VG.Proof.Argon2.AArch64.HPrime
