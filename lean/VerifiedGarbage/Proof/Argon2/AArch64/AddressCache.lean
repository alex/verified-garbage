import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheSelect
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheWord

/-! Complete cached random-word selection against RFC 9106's address block. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Spec.Argon2 VG.Impl.Argon2.AArch64.AddressCache

structure Done (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  selected : Selected s t p pass lane slice
  random : t.gpr .x0 =
    (addressBlock p pass lane slice (wanted s))[(s.gpr .x23).toNat % 128]'(Nat.mod_lt _ (by decide))

theorem code_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa code s (Done s · p pass lane slice) := by
  unfold code
  refine WP.seq ((selected_ok p pass lane slice old s h).mono ?_)
  intro a selected
  refine (word_ok a selected.layout).mono ?_
  rintro t ⟨random, keeps⟩
  have regs : ∀ r ∈ FillCompress.loopRegs, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ∉ [Reg.x3, .x8, .x0, .x12, .x13, .x15] := by
      simp only [FillCompress.loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (keeps.regs r ne).trans (selected.regs r hr)
  have bp := keeps.regs .x19 (by decide)
  have sp := keeps.sp
  have work' : AddressCalls.work t = AddressCalls.work a := by
    unfold AddressCalls.work; rw [bp, keeps.mem]
  have layout : AddressCalls.Ready t := by
    constructor
    · rw [keeps.rd, keeps.wr, bp]; exact selected.layout.frameRead
    · rw [work', keeps.wr]; exact selected.layout.workWrite
    · rw [bp, work']; exact selected.layout.frameWork
    · rw [bp, sp]; exact selected.layout.frameStack
    · rw [sp, work']; exact selected.layout.stackWork
  refine ⟨⟨?_, layout, work'.trans selected.work_eq, regs,
    keeps.rd.trans selected.rd, keeps.wr.trans selected.wr, ?_,
    keeps.sp.trans selected.sp, ?_⟩, ?_⟩
  · rw [keeps.mem]; exact selected.block
  · rw [keeps.mem]; exact selected.frame
  · rw [bp, keeps.mem]; exact selected.counterWord
  · rw [selected.work_eq, selected.regs .x23 (by simp [FillCompress.loopRegs]), selected.block] at random
    exact random

end VG.Proof.Argon2.AArch64.AddressCache
