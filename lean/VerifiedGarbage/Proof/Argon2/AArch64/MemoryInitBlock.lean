import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitArgs
import VerifiedGarbage.Proof.Argon2.AArch64.MemoryInitCall

/-! # Initializing a block while preserving H₀ and the public lane counters -/

namespace VG.Proof.Argon2.AArch64.MemoryInit

open VG VG.AArch64 VG.Impl.Argon2.AArch64.MemoryInit
open VG.Spec.Blake2 (bytesAt)

structure BlockReady (s : State) : Prop where
  stackMinimum : 16 ≤ s.sp.toNat
  input : Covers [⟨s.gpr .x19, 72⟩] s.wr
  output : Covers [⟨s.gpr .x22, 1024⟩] s.wr
  work : (⟨s.gpr .x24, 16384⟩ : Region) ∈ s.wr
  frameWork : (⟨s.gpr .x19, 72⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  frameOutput : (⟨s.gpr .x19, 72⟩ : Region).Disjoint ⟨s.gpr .x22, 1024⟩
  outputWork : (⟨s.gpr .x22, 1024⟩ : Region).Disjoint ⟨s.gpr .x24, 16384⟩
  stackFrame : (below (s.sp) 16).Disjoint ⟨s.gpr .x19, 72⟩
  stackOutput : (below (s.sp) 16).Disjoint ⟨s.gpr .x22, 1024⟩
  stackWork : (below (s.sp) 16).Disjoint ⟨s.gpr .x24, 16384⟩

theorem BlockArgs.regs {s t : State} {column : Nat} (h : BlockArgs s t column)
    (r : Reg) (hr : r ∈ FillCompress.loopRegs) : t.gpr r = s.gpr r := by
  have hn : r ≠ .x8 ∧ r ≠ .x0 ∧ r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x3 ∧ r ≠ .x4 := by
    simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  exact h.other r hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2

theorem BlockReady.prefix {s : State} (h : BlockReady s) (d : Nat)
    (bound : d + 4 ≤ 72) : InRegions s.wr (s.gpr .x19 + BitVec.ofNat 64 d) 4 := by
  exact h.input _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ bound (by omega)⟩

theorem BlockArgs.ready {s t : State} {column : Nat} (a : BlockArgs s t column)
    (h : BlockReady s) : CallReady t := by
  have base := a.regs .x24 (by decide)
  have sp := a.sp
  refine ⟨by rw [sp]; exact h.stackMinimum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a.input, a.rd, a.wr]
    intro p n ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst r
    obtain ⟨r, hr, hc'⟩ := h.input p n ⟨_, List.mem_singleton_self _, hc⟩
    exact ⟨r, List.mem_append_right _ hr, hc'⟩
  · rw [a.output, a.wr]; exact h.output
  · rw [a.work, a.wr]; exact h.work
  · rw [a.input, a.work]; exact h.frameWork
  · rw [a.output, a.work]; exact h.outputWork
  · rw [sp, a.input]; exact h.stackFrame
  · rw [sp, a.output]; exact h.stackOutput
  · rw [sp, a.work]; exact h.stackWork

structure BlockDone (s t : State) (column : Nat) : Prop where
  digest : bytesAt t.mem (s.gpr .x22) 1024 = Spec.Argon2.hPrime 1024
    (bytesAt s.mem (s.gpr .x19) 64 ++ Spec.Argon2.le32 column ++ Spec.Argon2.le32 (s.gpr .x20).toNat)
  regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r
  sp : t.sp = s.sp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [⟨s.gpr .x22, 1024⟩, ⟨s.gpr .x24, 16384⟩,
    below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem t.mem

theorem block_ok (v : HPrime.Backend) (name : String)
    (s : State) (column : Nat) (columnBound : column < 65536) (h : BlockReady s) :
    WP isa (block name v.hash column) s (fun t => BlockDone s t column) := by
  unfold block
  refine WP.seq ((blockArgs_ok s column columnBound
    (by simpa only [show BitVec.ofNat 64 64 = (64 : Addr) from rfl] using h.prefix 64 (by decide))
    (by simpa only [show BitVec.ofNat 64 68 = (68 : Addr) from rfl] using h.prefix 68 (by decide))).mono ?_)
  intro a ha
  refine (hPrime_call_ok v name a (ha.ready h) ha.inputLength ha.outputLength).mono ?_
  intro t ht
  refine ⟨?_, fun r hr => (ht.regs r hr).trans (ha.regs r hr),
    ht.sp.trans ha.sp, ht.rd.trans ha.rd, ht.wr.trans ha.wr, ?_⟩
  · have digest := ht.digest
    rw [ha.output, ha.input, ha.mem, blockMem_bytes] at digest
    exact digest
  · have argsFrame : Frame [⟨s.gpr .x22, 1024⟩, ⟨s.gpr .x24, 16384⟩,
        below (s.sp) 16, ⟨s.gpr .x19 + 64, 8⟩] s.mem a.mem := by
      rw [ha.mem]
      exact (blockMem_frame _ _ _ _).mono (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_singleton_self _))))
    apply argsFrame.trans
    have frame := ht.frame
    rw [ha.output, ha.work, ha.sp] at frame
    exact frame.mono (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))

end VG.Proof.Argon2.AArch64.MemoryInit
