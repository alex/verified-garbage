import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheState

/-! Cache validity does not depend on the current index, so advancing an index
retains it. Counter zero requires no cached contents; every other counter
identifies its specified independent-address block.
-/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

structure Invariant (p : Params) (pass lane slice old : Nat) (s : State) : Prop where
  layout : AddressCalls.Ready s
  reads : ∀ d ∈ [0, 8, 72, 112, 240], InRegions (s.rd ++ s.wr) (off (s.gpr .rbp) d) 8
  write : InRegions s.wr (off (s.gpr .rbp) 8) 8
  words : AddressHeader.Words p pass lane slice old s
  bound : old < 2 ^ 64
  cached : old = 0 ∨ blockAt s.mem (off (AddressCalls.work s) 6144) = addressBlock p pass lane slice old

theorem wanted_bound (s : State) : wanted s < 2 ^ 64 := by
  unfold wanted
  have := (s.gpr .r15).isLt
  omega

theorem Invariant.ready {p : Params} {pass lane slice old : Nat} {s : State}
    (h : Invariant p pass lane slice old s) : Ready p pass lane slice old s := by
  refine ⟨h.layout, h.reads, h.write, h.words, ?_⟩
  intro same
  have word : BitVec.ofNat 64 (wanted s) = BitVec.ofNat 64 old := by
    unfold wanted
    rw [← counter_nat]; exact same.trans h.words.counterWord
  have equal := (ReferenceMap.word_eq _ _ (wanted_bound s) h.bound).mp word
  rcases h.cached with zero | cached
  · exfalso
    exact counter_ne_zero _ (same.trans (h.words.counterWord.trans (by rw [zero]; rfl)))
  · rw [← equal] at cached
    exact cached

theorem Selected.invariant {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : Ready p pass lane slice old s) (h : Selected s t p pass lane slice) :
    Invariant p pass lane slice (wanted s) t := by
  have bp := h.regs .rbp (by simp [calleeSaved])
  refine ⟨h.layout, ?_, ?_, h.words ready, wanted_bound s, Or.inr ?_⟩
  · rw [h.rd, h.wr, bp]; exact ready.reads
  · rw [h.wr, bp]; exact ready.write
  · rw [h.work_eq]; exact h.block

theorem Invariant.zero {p : Params} {pass lane slice : Nat} {s : State}
    (h : Ready p pass lane slice 0 s) : Invariant p pass lane slice 0 s :=
  ⟨h.layout, h.reads, h.write, h.words, by decide, Or.inl rfl⟩

theorem Invariant.of_state {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s)
    (regs : ∀ r ∈ [Reg.rsp, .rbp, .rbx, .r14], t.gpr r = s.gpr r)
    (mem : t.mem = s.mem) (rd : t.rd = s.rd) (wr : t.wr = s.wr) :
    Invariant p pass lane slice old t := by
  have bp := regs .rbp (by simp)
  have sp := regs .rsp (by simp)
  have work : AddressCalls.work t = AddressCalls.work s := by
    unfold AddressCalls.work; rw [mem, bp]
  refine ⟨?_, ?_, ?_, ?_, h.bound, ?_⟩
  · constructor
    · rw [rd, wr, bp]; exact h.layout.frameRead
    · rw [wr, work]; exact h.layout.workWrite
    · rw [bp, work]; exact h.layout.frameWork
    · rw [bp, sp]; exact h.layout.frameStack
    · rw [sp, work]; exact h.layout.stackWork
  · rw [rd, wr, bp]; exact h.reads
  · rw [wr, bp]; exact h.write
  · exact ⟨by rw [mem, bp]; exact h.words.passWord,
      (regs .rbx (by simp)).trans h.words.laneWord,
      (regs .r14 (by simp)).trans h.words.sliceWord,
      by rw [mem, bp]; exact h.words.blocksWord,
      by rw [mem, bp]; exact h.words.passesWord,
      by rw [mem, bp]; exact h.words.variantWord,
      by rw [mem, bp]; exact h.words.counterWord⟩
  · rw [mem, work]; exact h.cached

theorem Invariant.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Invariant p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Invariant p pass lane slice old t := by
  apply h.of_state _ k.mem k.rd k.wr
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact k.regs _ (by decide)

end VG.Proof.Argon2.X86_64.AddressCache
