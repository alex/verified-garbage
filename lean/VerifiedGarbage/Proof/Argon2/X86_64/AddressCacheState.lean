import VerifiedGarbage.Proof.Argon2.X86_64.AddressCache
import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelStable

/-! Retain the filling header and allocation across independent-address regeneration. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2

theorem Selected.frame_word {s t : State} {p : Params} {pass lane slice : Nat}
    (layout : AddressCalls.Ready s) (h : Selected s t p pass lane slice)
    (d : Nat) (bound : d + 8 ≤ 272) (separate : d + 8 ≤ 8 ∨ 16 ≤ d) :
    t.mem.readW (off (t.gpr .rbp) d) 64 = s.mem.readW (off (s.gpr .rbp) d) 64 := by
  rw [h.regs .rbp (by simp [calleeSaved])]
  have sub : Region.Sub ⟨off (s.gpr .rbp) d, 8⟩ ⟨s.gpr .rbp, 272⟩ := Offset.sub_base _ bound
  exact h.frame.readW (r := ⟨off (s.gpr .rbp) d, 8⟩) (Region.contains_self _ _) (by
    intro r hr
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact layout.frameWork.sub_left sub
    · exact layout.frameStack.sub_left sub
    · exact Offset.disjoint _ separate (by omega) (by decide)) (by decide)

theorem Selected.words {s t : State} {p : Params} {pass lane slice old : Nat}
    (ready : Ready p pass lane slice old s) (h : Selected s t p pass lane slice) :
    AddressHeader.Words p pass lane slice (wanted s) t := by
  exact ⟨(h.frame_word ready.layout 0 (by decide) (by decide)).trans ready.words.passWord,
    (h.regs .rbx (by simp [calleeSaved])).trans ready.words.laneWord,
    (h.regs .r14 (by simp [calleeSaved])).trans ready.words.sliceWord,
    (h.frame_word ready.layout 240 (by decide) (by decide)).trans ready.words.blocksWord,
    (h.frame_word ready.layout 72 (by decide) (by decide)).trans ready.words.passesWord,
    (h.frame_word ready.layout 112 (by decide) (by decide)).trans ready.words.variantWord,
    h.counterWord.trans (counter_nat _)⟩

theorem Ready.of_keeps {p : Params} {pass lane slice old : Nat} {s t : State}
    (h : Ready p pass lane slice old s) (k : Divide.Keeps ReferenceMap.changed s t) :
    Ready p pass lane slice old t := by
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    apply k.regs
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have stable := AddressCalls.stable_of_frame h.layout regs k.rd k.wr
    (by rw [k.mem]; exact Frame.refl _ _) k.mxcsr
  refine ⟨stable.ready, stable.reads h.reads, ?_, stable.words h.layout h.words, ?_⟩
  · rw [k.wr, k.regs .rbp (by decide)]; exact h.write
  · intro same
    have wanted' : wanted t = wanted s := by unfold wanted; rw [k.regs .r15 (by decide)]
    rw [k.mem, k.regs .rbp (by decide), k.regs .r15 (by decide)] at same
    rw [k.mem, stable.work_eq, wanted']
    exact h.cached same

end VG.Proof.Argon2.X86_64.AddressCache
