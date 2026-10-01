import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheSelect
import VerifiedGarbage.Proof.Argon2.X86_64.AddressCacheWordCT

/-! Cache regeneration branches only on public counters. -/

namespace VG.Proof.Argon2.X86_64.AddressCache

open VG VG.X86_64 VG.Impl.Argon2.X86_64.AddressCache

structure CacheRelated (s t : State) : Prop where
  prepare : AddressCalls.PrepareRelated s t
  indices : s.gpr .r15 = t.gpr .r15
  counters : s.mem.readW (off (s.gpr .rbp) 8) 64 = t.mem.readW (off (t.gpr .rbp) 8) 64
  leftWrite : InRegions s.wr (off (s.gpr .rbp) 8) 8
  rightWrite : InRegions t.wr (off (t.gpr .rbp) 8) 8

structure CheckedRelated (s t : State) : Prop where
  related : CacheRelated s t
  values : s.gpr .rax = t.gpr .rax
  flags : s.zf = t.zf

theorem check_rel : RelCT isa
    (fun s t => ∀ r ∈ [Reg.rbp, .r15], s.gpr r = t.gpr r)
    (.block check) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp, .r15])
    (fun _ _ h => Taint.agree_ofRegs h) (by taint_decide)

theorem check_public_rel : RelCT isa CacheRelated (.block check) CheckedRelated := by
  have trace := check_rel.mono (P' := CacheRelated) (by
    intro s t h r hr
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
  have index : a.gpr .r15 = b.gpr .r15 := (sa.regs .r15 (by simp [calleeSaved])).trans
    (hp.indices.trans (sb.regs .r15 (by simp [calleeSaved])).symm)
  have counters : a.mem.readW (off (a.gpr .rbp) 8) 64 = b.mem.readW (off (b.gpr .rbp) 8) 64 := by
    rw [ka.mem, kb.mem, sa.regs .rbp (by simp [calleeSaved]), sb.regs .rbp (by simp [calleeSaved])]
    exact hp.counters
  refine ⟨⟨⟨hp.prepare.related.of_stable sa sb, sa.reads hp.prepare.leftReads,
    sb.reads hp.prepare.rightReads⟩, index, counters, ?_, ?_⟩, ?_, ?_⟩
  · rw [ka.wr, sa.regs .rbp (by simp [calleeSaved])]; exact hp.leftWrite
  · rw [kb.wr, sb.regs .rbp (by simp [calleeSaved])]; exact hp.rightWrite
  · rw [va, vb, hp.indices]
  · rw [fa, fb, hp.indices, hp.counters]

theorem save_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    (.block save) (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst r
      exact h)) (by taint_decide)

theorem save_public_rel : RelCT isa CheckedRelated (.block save) AddressCalls.PrepareRelated := by
  have trace := save_rel.mono (P' := CheckedRelated)
    (fun _ _ h => h.related.prepare.related.bases) (fun _ _ h => h)
  have full := trace.wpDep (fun s t h =>
    ⟨save_ready s h.related.prepare.related.left h.related.leftWrite,
      save_ready t h.related.prepare.related.right h.related.rightWrite⟩)
  refine full.mono (fun _ _ h => h) ?_
  intro a b h
  obtain ⟨_, s, t, hp, ha, hb⟩ := h
  refine ⟨⟨ha.ready, hb.ready, ?_, ?_, ha.work_eq.trans
    (hp.related.prepare.related.work.trans hb.work_eq.symm)⟩, ?_, ?_⟩
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.bases
  · rw [ha.regs, hb.regs]; exact hp.related.prepare.related.stacks
  · rw [ha.rd, ha.wr, ha.regs]; exact hp.related.prepare.leftReads
  · rw [hb.rd, hb.wr, hb.regs]; exact hp.related.prepare.rightReads

theorem select_trace : RelCT isa CacheRelated select (fun _ _ => True) := by
  have noop : RelCT isa (fun _ _ : State => True) (.block []) (fun _ _ => True) :=
    RelCT.taint (A := taint) (Taint.ofRegs [])
      (fun _ _ _ => Taint.agree_ofRegs (by intro r hr; simp at hr)) (by taint_decide)
  have branches : RelCT isa CheckedRelated
      (.ite .e (.block []) (.seq (.block save) Impl.Argon2.X86_64.AddressCalls.code))
      (fun _ _ => True) :=
    RelCT.ite (by intro s t h; simp only [eval, h.flags])
      (noop.mono (fun _ _ _ => trivial) (fun _ _ h => h))
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
  · exact (ha.regs .rbp (by simp [calleeSaved])).trans
      (hp.pubs.prepare.related.bases.trans (hb.regs .rbp (by simp [calleeSaved])).symm)
  · exact (ha.regs .rsp (by simp [calleeSaved])).trans
      (hp.pubs.prepare.related.stacks.trans (hb.regs .rsp (by simp [calleeSaved])).symm)
  · exact (ha.regs .r15 (by simp [calleeSaved])).trans
      (hp.pubs.indices.trans (hb.regs .r15 (by simp [calleeSaved])).symm)

theorem code_rel (p : Spec.Argon2.Params) (pass lane slice old : Nat) :
    RelCT isa (ReadyRelated p pass lane slice old) code (fun _ _ => True) :=
  (select_public_rel p pass lane slice old).seq word_rel

end VG.Proof.Argon2.X86_64.AddressCache
