import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Body

/-! # Frames for successive ECB blocks -/

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64

def stepWrites (s : State) : List Region := [dataR s, ⟨s.gpr .x2, 512⟩]

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, ⟨s.gpr .x2, 512⟩]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n)
    (buf : s'.gpr .x2 = s.gpr .x2)
    (ptr : s'.gpr .x1 = s.gpr .x1 + BitVec.ofNat 64 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨s'.gpr .x1, 8 * m⟩ ⟨s.gpr .x1, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨s.gpr .x2, 512⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn rfl (by simp)

theorem BodyPost.schedule {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .x0) = Spec.TripleDes.scheduleAt s.mem (s.gpr .x0) := by
  apply VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyData
      (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem BodyPost.tailData {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.TripleDes.blocksAt s'.mem (s.gpr .x1 + 8) n = Spec.TripleDes.blocksAt s.mem (s.gpr .x1 + 8) n := by
  have sub : Region.Sub ⟨s.gpr .x1 + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (s.gpr .x1 + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

theorem firstBlock_frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) :
    Spec.TripleDes.blockAt m (s.gpr .x1) = Spec.TripleDes.blockAt s'.mem (s.gpr .x1) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (dataR s).Disjoint ⟨s.gpr .x1 + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ frame
  have buf := h.reg .x2 (by decide) (by decide) (by decide)
  simpa only [loopWrites, dataR, buf, h.ptr,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))

end VG.Proof.TripleDes.AArch64.Ecb
