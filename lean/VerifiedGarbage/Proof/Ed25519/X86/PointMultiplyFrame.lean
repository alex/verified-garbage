import VerifiedGarbage.Proof.Ed25519.X86.PointMulBatch

/-! Untrusted: complete point multiplication preserves API pointers and scalar bits. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure MulKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x 24 7144] s.mem t.mem

theorem MulKeep.refl (x : BitVec 32) (s : State) : MulKeep x s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
theorem MulKeep.ctx {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr
theorem MulKeep.trans {x : BitVec 32} {s t u : State} (h : MulKeep x s t) (k : MulKeep x t u) :
    MulKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem MulKeep.of_powers {x : BitVec 32} {s t : State} {o n : Nat} (hc : Ctx x s)
    (h : PowersKeep x o n s t) (ho : 24 ≤ o) (hn : o + n ≤ 7168) : MulKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  refine ⟨sub x 24 7144, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact sub_sub hc.fit ho (by omega) (by omega)

theorem MulKeep.of_batch {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : BatchKeep x s t) :
    MulKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  refine ⟨sub x 24 7144, List.mem_singleton_self _, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)
  · exact sub_sub hc.fit (by decide) (by decide) (by decide)

theorem MulKeep.of_ikeep {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : IKeep x s t) :
    MulKeep x s t := MulKeep.of_powers hc (PowersKeep.of_ikeep h 24 0) (by decide) (by decide)

theorem MulKeep.bit {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  rw [List.mem_singleton.mp hr]
  exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit])
    (Or.inr (by omega)) : (sub x (7168 + i) 1).Disjoint (sub x 24 7144)) _ (Region.contains_self _ _)

theorem MulKeep.word {x : BitVec 32} {s t : State} (h : MulKeep x s t) (hc : Ctx x s)
    (o : Nat) (ho : o + 4 ≤ 24) : wd t.mem x o = wd s.mem x o :=
  wd_frame1 h.frame hc.fit (by decide) (by omega) (Or.inl ho)

end VG.Proof.Ed25519.X86
