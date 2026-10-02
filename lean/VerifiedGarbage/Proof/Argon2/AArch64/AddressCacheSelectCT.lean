import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheSelect
import VerifiedGarbage.Proof.Argon2.AArch64.AddressCacheWordCT

/-! Cache regeneration branches only on public counters. -/

namespace VG.Proof.Argon2.AArch64.AddressCache

open VG VG.AArch64 VG.Impl.Argon2.AArch64.AddressCache

structure CacheRelated (s t : State) : Prop where
  prepare : AddressCalls.PrepareRelated s t
  indices : s.gpr .x23 = t.gpr .x23
  counters : s.mem.readW (off (s.gpr .x19) 8) 64 = t.mem.readW (off (t.gpr .x19) 8) 64
  leftWrite : InRegions s.wr (off (s.gpr .x19) 8) 8
  rightWrite : InRegions t.wr (off (t.gpr .x19) 8) 8

structure CheckedRelated (s t : State) : Prop where
  related : CacheRelated s t
  values : s.gpr .x8 = t.gpr .x8
  flags : s.gpr .x15 = t.gpr .x15

theorem check_rel : RelCT isa
    (fun s t => s.sp = t.sp ∧ ∀ r ∈ [Reg.x19, .x23], s.gpr r = t.gpr r)
    (.block check) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19, .x23])
    (fun _ _ h => ⟨h.1, fun r hr => h.2 r (by simpa only [Taint.mem_ofRegs] using hr)⟩)
    [] (by taint_decide)).mono (fun _ _ h => h) (fun _ _ h => h.1)

theorem check_public_rel : RelCT isa CacheRelated (.block check) CheckedRelated := by
  have trace := check_rel.mono (P' := CacheRelated) (by
    intro s t h
    refine ⟨h.prepare.related.stacks, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact h.prepare.related.bases
    · exact h.indices) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨check_ok s (h.prepare.leftReads 8 (by simp)), check_ok t (h.prepare.rightReads 8 (by simp))⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ⟨va, fa, ka⟩, ⟨vb, fb, kb⟩⟩ := h
  have sa := check_stable hp.prepare.related.left ka
  have sb := check_stable hp.prepare.related.right kb
  have index : a.gpr .x23 = b.gpr .x23 := (sa.regs .x23 (by simp [FillCompress.loopRegs])).trans
    (hp.indices.trans (sb.regs .x23 (by simp [FillCompress.loopRegs])).symm)
  have counters : a.mem.readW (off (a.gpr .x19) 8) 64 = b.mem.readW (off (b.gpr .x19) 8) 64 := by
    rw [ka.mem, kb.mem, sa.regs .x19 (by simp [FillCompress.loopRegs]), sb.regs .x19 (by simp [FillCompress.loopRegs])]
    exact hp.counters
  refine ⟨⟨⟨hp.prepare.related.of_stable sa sb, sa.reads hp.prepare.leftReads,
    sb.reads hp.prepare.rightReads⟩, index, counters, ?_, ?_⟩, ?_, ?_⟩
  · rw [ka.wr, sa.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.leftWrite
  · rw [kb.wr, sb.regs .x19 (by simp [FillCompress.loopRegs])]; exact hp.rightWrite
  · rw [va, vb, hp.indices]
  · rw [fa, fb, hp.indices, hp.counters]

theorem save_rel : RelCT isa (fun s t => s.gpr .x19 = t.gpr .x19 ∧ s.sp = t.sp)
    (.block save) (fun s t => s.sp = t.sp) :=
  (RelCT.taintRegs (τ := Taint.ofRegs [.x19])
    (fun _ _ h => ⟨h.2, by
      intro r hr
      simp only [Taint.mem_ofRegs, List.mem_singleton] at hr
      subst r
      exact h.1⟩) [] (by taint_decide)).mono
    (fun _ _ h => h) (fun _ _ h => h.1)

theorem save_public_rel : RelCT isa CheckedRelated (.block save) AddressCalls.PrepareRelated := by
  have trace := save_rel.mono (P' := CheckedRelated)
    (fun _ _ h => ⟨h.related.prepare.related.bases, h.related.prepare.related.stacks⟩) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨save_ready s h.related.prepare.related.left h.related.leftWrite,
      save_ready t h.related.prepare.related.right h.related.rightWrite⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ha.work_eq.trans
    (hp.related.prepare.related.work.trans hb.work_eq.symm)⟩, ?_, ?_⟩
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.bases
  · exact ha.sp.trans (hp.related.prepare.related.stacks.trans hb.sp.symm)
  · rw [ha.rd, ha.wr, ha.regs]; exact hp.related.prepare.leftReads
  · rw [hb.rd, hb.wr, hb.regs]; exact hp.related.prepare.rightReads

theorem select_trace : RelCT isa CacheRelated select (fun _ _ => True) := by
  have noop : RelCT isa (fun s t : State => s.sp = t.sp) (.block []) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ h => ⟨h, by simp [Taint.mem_ofRegs]⟩) (by taint_decide)
  have branches : RelCT isa CheckedRelated
      (.ite (.zero .x .x15) (.block []) (.seq (.block save) Impl.Argon2.AArch64.AddressCalls.code))
      (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, State.read, h.flags])
      (noop.mono (fun _ _ h => h.1.related.prepare.related.stacks) (fun _ _ h => h))
      ((save_public_rel.seq AddressCalls.code_rel).mono (fun _ _ h => h.1) (fun _ _ _ => trivial))
  exact check_public_rel.seq branches

structure ReadyRelated (p : Spec.Argon2.Params) (pass lane slice old : Nat) (s t : State) : Prop where
  left : Ready p pass lane slice old s
  right : Ready p pass lane slice old t
  pubs : CacheRelated s t

theorem select_public_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (ReadyRelated p pass lane slice old) select WordRelated := by
  have trace := select_trace.mono (P' := ReadyRelated p pass lane slice old)
    (fun _ _ h => h.pubs) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨selected_ok p pass lane slice old s h.left, selected_ok p pass lane slice old t h.right⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.layout, hb.layout, ?_, ?_, ha.work_eq.trans
    (hp.pubs.prepare.related.work.trans hb.work_eq.symm)⟩, ?_⟩
  · exact (ha.regs .x19 (by simp [FillCompress.loopRegs])).trans
      (hp.pubs.prepare.related.bases.trans (hb.regs .x19 (by simp [FillCompress.loopRegs])).symm)
  · exact ha.sp.trans (hp.pubs.prepare.related.stacks.trans hb.sp.symm)
  · exact (ha.regs .x23 (by simp [FillCompress.loopRegs])).trans
      (hp.pubs.indices.trans (hb.regs .x23 (by simp [FillCompress.loopRegs])).symm)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (ReadyRelated p pass lane slice old) code (fun s t => s.sp = t.sp) :=
  (select_public_rel p pass lane slice old).seq word_rel

end VG.Proof.Argon2.AArch64.AddressCache
