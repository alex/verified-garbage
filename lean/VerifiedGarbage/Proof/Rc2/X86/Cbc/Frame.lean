import VerifiedGarbage.Proof.Rc2.X86.Cbc.Pre

/-! # The frame preserved by a CBC step -/

namespace VG.Proof.Rc2.X86.Cbc

open VG VG.X86

def stepWrites (s : State) : List Region := [ivR s, dataR s, ⟨addr32 (s.gpr .ebp), 264⟩, stackR s]

structure Pinned (s s' : State) : Prop where
  reg : ∀ r ∈ kept, s'.gpr r = s.gpr r
  callee : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Frame (stepWrites s) s.mem s'.mem

theorem Pinned.of_keep {s s' : State} {m : Mem} (h : Keep [.eax, .edx] {s with mem := m} s')
    (frame : Frame (stepWrites s) s.mem m) : Pinned s s' := by
  have k : ∀ r ∈ kept, r ∉ [.eax, .edx] := by decide
  have c : ∀ r ∈ calleeSaved, r ∉ [.eax, .edx] := by decide
  exact ⟨fun r hr => h.reg r (k r hr), fun r hr => h.reg r (c r hr), h.rd, h.wr, by rw [h.mem]; exact frame⟩

theorem Pinned.of_call {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') : Pinned s s' := by
  refine ⟨h.reg, h.callee, h.rd, h.wr, h.mem.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨dataR s, by simp [stepWrites], fun _ h => h⟩
  · exact ⟨⟨addr32 (s.gpr .ebp), 264⟩, by simp [stepWrites], Region.sub_prefix (by decide)⟩
  · exact ⟨stackR s, by simp [stepWrites], fun _ h => h⟩

theorem Pinned.writes_eq {s s' : State} (h : Pinned s s') : stepWrites s' = stepWrites s := by
  simp only [stepWrites, ivR, dataR, stackR, h.reg .ecx (by decide), h.reg .esi (by decide),
    h.reg .ebp (by decide), h.reg .esp (by decide)]

theorem Pinned.trans {s s' s'' : State} (h : Pinned s s') (h' : Pinned s' s'') : Pinned s s'' := by
  refine ⟨fun r hr => (h'.reg r hr).trans (h.reg r hr), fun r hr => (h'.callee r hr).trans (h.callee r hr),
    h'.rd.trans h.rd, h'.wr.trans h.wr, ?_⟩
  have f := h'.mem
  rw [h.writes_eq] at f
  exact h.mem.trans f

theorem Pinned.pre {s s' : State} {n : Nat} (h : Pinned s s') (hp : StepPre s n) : StepPre s' n :=
  hp.transport h.rd h.wr h.reg

theorem Pinned.schedule {s s' : State} (h : Pinned s s') (hp : StepPre s) :
    Spec.Rc2.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply scheduleAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyIv (And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 264 ≤ 512))) hp.stackKey.symm))

theorem CallPost.iv {d : Spec.Rc2.Direction} {s s' : State} (h : CallPost d s s') (hp : StepPre s) :
    Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) = Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx)) := by
  apply blockAt_frame h.mem
  simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.ivData (And.intro
      (hp.ivBuf.sub_right (Region.sub_prefix (by decide : 256 ≤ 512))) hp.stackIv.symm)

structure StepPost (d : Spec.Rc2.Direction) (s s' : State) : Prop extends Pinned s s' where
  data : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .esi)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).1
  iv : Spec.Rc2.blockAt s'.mem (addr32 (s.gpr .ecx)) =
    (Spec.Rc2.cbcStep (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .ebx))) d
      (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .ecx))) (Spec.Rc2.blockAt s.mem (addr32 (s.gpr .esi)))).2

end VG.Proof.Rc2.X86.Cbc
