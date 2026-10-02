import VerifiedGarbage.Proof.Argon2.X86_64.FillKernelPrepare

/-! Complete active-cell update from a random word and the matrix allocation. -/

namespace VG.Proof.Argon2.X86_64.FillKernel

open VG VG.X86_64 VG.Spec.Argon2

def writes (s : State) (p : Params) (lane slice index : Nat) : List Region :=
  [⟨current s p lane slice index, 1024⟩, ⟨work s, 5120⟩,
    below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩]

structure Done (s t : State) (p : Params) (pass lane slice index : Nat) : Prop where
  block : blockAt t.mem (current s p lane slice index) =
    let next := Spec.Argon2.compress (blockAt s.mem (previous s p lane slice index))
      (blockAt s.mem (referenced s p pass lane slice index))
    if pass = 0 then next else xorBlock next (blockAt s.mem (current s p lane slice index))
  regs : ∀ r ∈ calleeSaved, t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame (writes s p lane slice index) s.mem t.mem
  mxcsr : t.mxcsr = s.mxcsr

theorem code_ok (s : State) (p : Params) (pass lane slice index : Nat)
    (h : Ready p pass lane slice index s) :
    WP isa Impl.Argon2.X86_64.FillKernel.code s (Done s · p pass lane slice index) := by
  unfold Impl.Argon2.X86_64.FillKernel.code
  refine WP.seq ((prepare_ok s p pass lane slice index h).mono ?_)
  intro b prepared
  have keeps := prepared.keeps
  have cur := prepared.currentPtr
  have prev := prepared.previousPtr
  have other := prepared.referencePtr
  refine (FillCompress.code_mx_ok b prepared.ready).mono ?_
  rintro t ⟨done, mx⟩
  have counter : FillCompress.pass b = BitVec.ofNat 64 pass := by
    unfold FillCompress.pass
    rw [keeps.mem, keeps.regs .rbp (by decide)]
    exact h.passWord
  refine ⟨?_, ?_, done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_, mx.trans keeps.mxcsr⟩
  · have block := done.block
    rw [cur, prev, other, keeps.mem, counter] at block
    simp only [ReferenceMap.word_zero pass (Nat.lt_trans h.bounds.passBound (by decide))] at block
    exact block
  · intro r hr
    have ne : r ∉ ReferenceMap.changed := by
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (done.regs r hr).trans (keeps.regs r ne)
  · have workB : FillCompress.work b = work s := by
      unfold FillCompress.work work
      rw [keeps.regs .rbp (by decide), keeps.mem]
    have frame := done.frame
    rw [FillCompress.writes, workB, cur, keeps.regs .rsp (by decide), keeps.regs .rbp (by decide), keeps.mem] at frame
    change Frame [⟨current s p lane slice index, 1024⟩, ⟨work s + 4096, 1024⟩,
      ⟨work s, 4096⟩, below (s.gpr .rsp) 8, ⟨off (s.gpr .rbp) 16, 8⟩] s.mem t.mem at frame
    apply frame.sub
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [writes], fun _ h => h⟩
    · exact ⟨⟨work s, 5120⟩, by simp [writes], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨work s, 5120⟩, by simp [writes], Region.sub_prefix (by decide)⟩
    · exact ⟨_, by simp [writes], fun _ h => h⟩
    · exact ⟨_, by simp [writes], fun _ h => h⟩

end VG.Proof.Argon2.X86_64.FillKernel
