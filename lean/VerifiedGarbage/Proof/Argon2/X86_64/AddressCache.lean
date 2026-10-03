import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheSelect
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheWord

/-! Complete cached random-word selection against RFC 9106's address block. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Spec.Argon2 VG.Impl.Argon2.X86_64.AddressCache

structure Done (s t : State) (p : Params) (pass lane slice : Nat) : Prop where
  selected : Selected s t p pass lane slice
  random : t.gpr .rdi =
    (addressBlock p pass lane slice (wanted s))[(s.gpr .r15).toNat % 128]'(Nat.mod_lt _ (by decide))

theorem code_ok (p : Params) (pass lane slice old : Nat) (s : State)
    (h : Ready p pass lane slice old s) :
    WP isa code s (Done s · p pass lane slice) := by
  unfold code
  refine WP.seq ((selected_ok p pass lane slice old s h).mono ?_)
  intro a selected
  refine (word_ok a selected.layout).mono ?_
  rintro t ⟨random, keeps⟩
  have regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r := by
    intro r hr
    have ne : r ∉ [Reg.rcx, .rax, .rdi] := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (keeps.regs r ne).trans (selected.regs r hr)
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
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
    keeps.mxcsr.trans selected.mxcsr, ?_⟩, ?_⟩
  · rw [keeps.mem]; exact selected.block
  · rw [keeps.mem]; exact selected.frame
  · rw [bp, keeps.mem]; exact selected.counterWord
  · rw [selected.work_eq, selected.regs .r15 (by simp [calleeSaved]), selected.block] at random
    exact random

end VG.Proof.Argon2.X86_64.AddressCache
