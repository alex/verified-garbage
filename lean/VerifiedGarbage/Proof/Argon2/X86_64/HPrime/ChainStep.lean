import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Next
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Output

/-! # H′: one hash-and-prefix iteration -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime
open VG.Proof.MdStream.X86_64 (wp_mov32i wp_cmpi)
open VG.Spec.Blake2 (bytesAt)

structure ChainStep (s t : State) : Prop where
  output : t.gpr .r14 = s.gpr .r14 + 32
  remaining : t.gpr .r15 = s.gpr .r15 - 32
  regs : ∀ r ∈ calleeSaved, r ≠ .r14 → r ≠ .r15 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .rbx, 832⟩, below (s.gpr .rsp) 16, ⟨s.gpr .r14, 32⟩] s.mem t.mem
  digest : bytesAt t.mem (s.gpr .rbx + 768) 64 =
    Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)
  bytes : bytesAt t.mem (s.gpr .r14) 32 =
    (Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64)).take 32
  cf : t.cf = some (decide ((s.gpr .r15 - 32).toNat < 65))

theorem chainStep_ok (v : Proof.Blake2.X86_64.Backend) (s : State)
    (work : (⟨s.gpr .rbx, 16384⟩ : Region) ∈ s.wr)
    (out : ∀ i < 32, InRegions s.wr (s.gpr .r14 + BitVec.ofNat 64 i) 1)
    (sep : (⟨s.gpr .rbx, 16384⟩ : Region).Disjoint ⟨s.gpr .r14, 32⟩)
    (stackWork : (below (s.gpr .rsp) 16).Disjoint ⟨s.gpr .rbx, 16384⟩) :
    WP isa (.seq (.block [.mov32 .rsi (.imm 64)])
      (.seq (next (hash v)) (.seq emitPrefix (.block [.alu .cmp .r15 (.imm 65)]))))
      s (ChainStep s) := by
  refine WP.seq (wp_mov32i fun a ha _ _ => WP.block_nil ?_)
  have ka : Keeps s a := by
    refine ⟨fun r hr => ?_, ha.rd, ha.wr, ?_⟩
    · have hn : r ≠ .rsi := by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact ha.other r hn
    · rw [ha.mem]; exact Frame.refl _ _
  have workA : (⟨a.gpr .rbx, 16384⟩ : Region) ∈ a.wr := by rw [ka.rbx, ka.wr]; exact work
  have stackA : (below (a.gpr .rsp) 16).Disjoint ⟨a.gpr .rbx, 16384⟩ := by
    rw [ka.rbx, ka.rsp]; exact stackWork
  have lengthA : (a.gpr .rsi).toNat = 64 := by rw [ha.gpr]; rfl
  refine WP.seq ((next_ok v a (by rw [lengthA]; decide) workA stackA).mono ?_)
  rintro u ⟨du, ku⟩
  have ksu := ka.trans ku
  have dstU : u.gpr .r14 = s.gpr .r14 := ksu.regs _ (by decide)
  have digestU : bytesAt u.mem (s.gpr .rbx + 768) 64 =
      Spec.Argon2.H 64 (bytesAt s.mem (s.gpr .rbx + 768) 64) := by
    simpa only [lengthA, ka.rbx, ha.mem, bytesAt_take _ _ 64 64 (by decide)] using du
  have workU : (⟨u.gpr .rbx, 16384⟩ : Region) ∈ u.wr := by rw [ksu.rbx, ksu.wr]; exact work
  have outU : ∀ i < 32, InRegions u.wr (u.gpr .r14 + BitVec.ofNat 64 i) 1 := by
    rw [ksu.wr, dstU]; exact out
  have sepU : (⟨u.gpr .rbx + 768, 32⟩ : Region).Disjoint ⟨u.gpr .r14, 32⟩ := by
    rw [ksu.rbx, dstU]
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 32 ≤ 16384))
  refine WP.seq ((emitPrefix_ok u workU outU sepU).mono ?_)
  intro w hw
  refine wp_cmpi fun t gt mt rt wt cf _ => WP.block_nil ?_
  have fw : Frame [⟨s.gpr .r14, 32⟩] u.mem w.mem := by
    rw [← dstU]; exact hw.frame
  refine ⟨?_, ?_, fun r hr h14 h15 => ?_, rt.trans (hw.rd.trans ksu.rd),
    wt.trans (hw.wr.trans ksu.wr), ?_, ?_, ?_, ?_⟩
  · rw [gt, hw.output, dstU]
  · rw [gt, hw.remaining, ksu.regs _ (by decide)]
  · rw [gt]
    have hrax : r ≠ .rax := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrcx : r ≠ .rcx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hrdx : r ≠ .rdx := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (hw.other r hrax hrcx hrdx h14 h15).trans (ksu.regs r hr)
  · rw [mt]
    apply Frame.trans (ksu.frame.sub ?_) (fw.sub ?_)
    · intro r hr
      exact ⟨r, List.mem_append_left _ hr, fun _ hx => hx⟩
    · intro r hr
      exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), fun _ hx => hx⟩
  · rw [mt, ← digestU]
    apply Proof.Blake2.bytesAt_congr
    intro i hi
    apply fw.bytes (R := ⟨s.gpr .rbx + 768, 64⟩) _ (show 64 ≤ 2 ^ 64 by decide) hi
    intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact sep.sub_left (Offset.sub_base _ (by decide : 768 + 64 ≤ 16384))
  · rw [mt, hw.mem, dstU, ksu.rbx, ← digestU, bytesAt_take _ _ 32 64 (by decide)]
    exact bytesAt_writeBytes _ _ _ (by simp only [bytesAt, List.length_map, List.length_range]; decide)
  · rw [cf, hw.remaining, ksu.regs _ (by decide)]
    rfl

end VG.Proof.Argon2.X86_64.HPrime
