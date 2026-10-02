import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Body

/-! # Frames for successive ECB blocks -/

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64

def stepWrites (s : State) : List Region := [dataR s, ⟨s.gpr .rdx, 512⟩, stackR s]

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, ⟨s.gpr .rdx, 512⟩, stackR s]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (buf : s'.gpr .rdx = s.gpr .rdx)
    (sp : s'.gpr .rsp = s.gpr .rsp) (ptr : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .rsi, 8 * m⟩ ⟨s.gpr .rsi, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨s.gpr .rdx, 512⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨stackR s, by simp [loopWrites], ?_⟩
    change Region.Sub (below (s'.gpr .rsp) 8) (below (s.gpr .rsp) 8)
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .rdi) = Spec.TripleDes.scheduleAt s.mem (s.gpr .rdi) := by
  apply VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyData (And.intro
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024))) hp.stackKey.symm)

theorem BodyPost.tailData {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.TripleDes.blocksAt s'.mem (s.gpr .rsi + 8) n = Spec.TripleDes.blocksAt s.mem (s.gpr .rsi + 8) n := by
  have sub : Region.Sub ⟨s.gpr .rsi + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (s.gpr .rsi + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep (And.intro
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
      ((hp.stackData.sub_right sub).symm))

theorem firstBlock_frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.TripleDes.blockAt m (s.gpr .rsi) = Spec.TripleDes.blockAt s'.mem (s.gpr .rsi) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (dataR s).Disjoint ⟨s.gpr .rsi + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ frame
  have buf := h.reg .rdx (by decide) (by decide) (by decide)
  have sp := h.reg .rsp (by decide) (by decide) (by decide)
  simpa only [loopWrites, dataR, stackR, buf, sp, h.ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep (And.intro
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
      ((hp.stackData.sub_right first).symm))

end VG.Proof.TripleDes.X86_64.Ecb
