import VerifiedGarbage.Proof.Ed25519.X86.PointBatch
import VerifiedGarbage.Proof.Ed25519.X86.AccumulateLoop

/-! One scalar batch preserves checkpoints, bits and saved API pointers. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure BatchKeep (x : BitVec 32) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : Frame [sub x 24 904, sub x 5120 2048] s.mem t.mem

theorem BatchKeep.ctx {x : BitVec 32} {s t : State} (h : BatchKeep x s t) (hc : Ctx x s) : Ctx x t :=
  hc.keep h.edi h.wr
theorem BatchKeep.trans {x : BitVec 32} {s t u : State} (h : BatchKeep x s t) (k : BatchKeep x t u) :
    BatchKeep x s u := ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd,
      k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem BatchKeep.of_powers {x : BitVec 32} {s t : State} (hc : Ctx x s)
    (h : PowersKeep x 5120 2048 s t) : BatchKeep x s t := by
  refine ⟨h.edi, h.esp, h.rd, h.wr, h.frame.sub ?_⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sub x 24 904, by simp, sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨sub x 24 904, by simp, sub_sub hc.fit (by decide) (by decide) (by decide)⟩
  · exact ⟨sub x 5120 2048, by simp, fun _ ha => ha⟩

theorem BatchKeep.of_ikeep {x : BitVec 32} {s t : State} (hc : Ctx x s) (h : IKeep x s t) :
    BatchKeep x s t := BatchKeep.of_powers hc (PowersKeep.of_ikeep h _ _)

theorem BatchKeep.of_counter {x : BitVec 32} {s t : State} (hc : Ctx x s)
    (he : t.gpr .edi = s.gpr .edi) (hs : t.gpr .esp = s.gpr .esp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [sub x 28 4] s.mem t.mem) : BatchKeep x s t :=
  ⟨he, hs, hr, hw, hf.sub fun r h => ⟨sub x 24 904, by simp, by
    rw [List.mem_singleton.mp h]; exact sub_sub hc.fit (by decide) (by decide) (by decide)⟩⟩

theorem BatchKeep.checkpoint {x : BitVec 32} {s t : State} (h : BatchKeep x s t) (hc : Ctx x s)
    (j : Nat) (hj : j < 32) : tablePoint t.mem x (1024 + 128 * j) = tablePoint s.mem x (1024 + 128 * j) := by
  apply table_point_of_words
  intro k hk
  apply wd_frame h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sub_disj (by omega_using [hc.fit, hj, hk]) (by omega_using [hc.fit]) (Or.inr (by omega))
  · exact sub_disj (by omega_using [hc.fit, hj, hk]) (by omega_using [hc.fit]) (Or.inl (by omega))

theorem BatchKeep.bit {x : BitVec 32} {s t : State} (h : BatchKeep x s t) (hc : Ctx x s)
    (i : Nat) (hi : i < 512) : t.mem (addr x (7168 + i)) = s.mem (addr x (7168 + i)) := by
  apply h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  have hb : (sub x (7168 + i) 1).Contains (addr x (7168 + i)) 1 := Region.contains_self _ _
  rcases hr with rfl | rfl
  · exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit]) (Or.inr (by omega))) _ hb
  · exact (sub_disj (by omega_using [hc.fit, hi]) (by omega_using [hc.fit]) (Or.inr (by omega))) _ hb

theorem PowersKeep.batch_index {x : BitVec 32} {s t : State} (hc : Ctx x s)
    (h : PowersKeep x 5120 2048 s t) : wd t.mem x 28 = wd s.mem x 28 := by
  apply wd_frame h.frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inr (by decide))
  · exact sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inl (by decide))
  · exact sub_disj (by omega_using [hc.fit]) (by omega_using [hc.fit]) (Or.inl (by decide))

end VG.Proof.Ed25519.X86
