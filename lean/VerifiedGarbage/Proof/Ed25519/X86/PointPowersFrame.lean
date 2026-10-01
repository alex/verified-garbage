import VerifiedGarbage.Proof.Ed25519.X86.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.X86.PointLoop

/-! Untrusted: frames for public counters, arithmetic and point tables. -/
namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def PowersFrame (x : BitVec 32) (o n : Nat) (m m' : Mem) : Prop :=
  Frame [sub x 24 4, sub x 64 864, sub x o n] m m'

structure PowersKeep (x : BitVec 32) (o n : Nat) (s t : State) : Prop where
  edi : t.gpr .edi = s.gpr .edi
  esp : t.gpr .esp = s.gpr .esp
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  frame : PowersFrame x o n s.mem t.mem

theorem PowersKeep.refl (x : BitVec 32) (o n : Nat) (s : State) : PowersKeep x o n s s :=
  ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩

theorem PowersKeep.ctx {x : BitVec 32} {o n : Nat} {s t : State}
    (h : PowersKeep x o n s t) (hc : Ctx x s) : Ctx x t := hc.keep h.edi h.wr

theorem PowersKeep.trans {x : BitVec 32} {o n : Nat} {s t u : State}
    (h : PowersKeep x o n s t) (k : PowersKeep x o n t u) : PowersKeep x o n s u :=
  ⟨k.edi.trans h.edi, k.esp.trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr, h.frame.trans k.frame⟩

theorem PowersFrame.mono {x : BitVec 32} {o n o' n' : Nat} {m m' : Mem}
    (h : PowersFrame x o n m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o' ≤ o) (hn : o + n ≤ o' + n') (hob : o < 8192) : PowersFrame x o' n' m m' := by
  apply h.sub
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨sub x 24 4, by simp, fun _ ha => ha⟩
  · exact ⟨sub x 64 864, by simp, fun _ ha => ha⟩
  · exact ⟨sub x o' n', by simp, sub_sub hx ho hn hob⟩

theorem PowersKeep.mono {x : BitVec 32} {o n o' n' : Nat} {s t : State}
    (h : PowersKeep x o n s t) (hc : Ctx x s)
    (ho : o' ≤ o) (hn : o + n ≤ o' + n') (hob : o < 8192) : PowersKeep x o' n' s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono hc.fit ho hn hob⟩

theorem PowersKeep.of_ikeep {x : BitVec 32} {s t : State} (h : IKeep x s t) (o n : Nat) :
    PowersKeep x o n s t :=
  ⟨h.edi, h.esp, h.rd, h.wr, h.frame.mono (fun _r hr => List.mem_cons_of_mem _
    (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr))))⟩

theorem PowersKeep.of_copy {x : BitVec 32} {o n : Nat} {s t : State} (h : CopyKeep x o n s t) :
    PowersKeep x o n s t :=
  ⟨h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr,
    h.frame.mono (fun _r hr => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))⟩

theorem PowersKeep.of_counter {x : BitVec 32} {s t : State} (o n : Nat)
    (he : t.gpr .edi = s.gpr .edi) (hs : t.gpr .esp = s.gpr .esp)
    (hr : t.rd = s.rd) (hw : t.wr = s.wr) (hf : Frame [sub x 24 4] s.mem t.mem) :
    PowersKeep x o n s t :=
  ⟨he, hs, hr, hw, hf.mono (fun _r h => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h)))⟩

theorem workspace_counter {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s) :
    wd t.mem x 24 = wd s.mem x 24 :=
  wd_frame1 h.frame hc.fit (by decide) (by decide) (Or.inl (by decide))

theorem workspace_table {x : BitVec 32} {s t : State} (h : IKeep x s t) (hc : Ctx x s)
    (o : Nat) (hlo : 928 ≤ o) (ho : o + 128 ≤ 8192) :
    tablePoint t.mem x o = tablePoint s.mem x o :=
  tablePoint_frame hc.fit h.frame (by decide) ho (Or.inr hlo)

theorem PowersFrame.table {x : BitVec 32} {o n a : Nat} {m m' : Mem}
    (h : PowersFrame x o n m m') (hx : x.toNat + 8192 ≤ 2 ^ 32)
    (ho : o + n ≤ 8192) (ha : a + 128 ≤ 8192) (hlo : 928 ≤ a)
    (hsep : a + 128 ≤ o ∨ o + n ≤ a) : tablePoint m' x a = tablePoint m x a := by
  apply table_point_of_words
  intro k hk
  apply wd_frame h
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
  · exact sub_disj (by omega) (by omega) (Or.inr (by omega))
  · exact sub_disj (by omega) (by omega) (by omega)

end VG.Proof.Ed25519.X86
