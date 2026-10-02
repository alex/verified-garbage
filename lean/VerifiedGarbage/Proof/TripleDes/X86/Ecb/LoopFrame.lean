import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Body

/-! # Frames for successive ECB blocks -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

def stepWrites (s : State) : List Region := [dataR s, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16]

def loopWrites (s : State) (n : Nat) : List Region := [dataR s n, ⟨addr32 (s.gpr .ebp), 512⟩, below (s.gpr .esp) 16]

theorem loopFrame_slice {s s' : State} {n m i : Nat} {a b : Mem}
    (h : Frame (loopWrites s' m) a b) (bound : i + m ≤ n) (fit : (s.gpr .esi).toNat + 8 * i < 2 ^ 32)
    (buf : s'.gpr .ebp = s.gpr .ebp)
    (sp : s'.gpr .esp = s.gpr .esp)
    (ptr : s'.gpr .esi = s.gpr .esi + BitVec.ofNat 32 (8 * i)) :
    Frame (loopWrites s n) a b := by
  apply h.sub
  intro r hr
  simp only [loopWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · refine ⟨dataR s n, by simp [loopWrites], ?_⟩
    change Region.Sub ⟨addr32 (s'.gpr .esi), 8 * m⟩ ⟨addr32 (s.gpr .esi), 8 * n⟩
    rw [ptr, addr_add fit]
    exact Offset.sub_base _ (by omega)
  · refine ⟨⟨addr32 (s.gpr .ebp), 512⟩, by simp [loopWrites], ?_⟩
    rw [buf]; exact fun _ h => h
  · refine ⟨below (s.gpr .esp) 16, by simp [loopWrites], ?_⟩
    rw [sp]; exact fun _ h => h

theorem BodyPost.frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hn : 1 ≤ n) : Frame (loopWrites s n) s.mem s'.mem :=
  loopFrame_slice (m := 1) (i := 0) h.mem hn (s.gpr .esi).isLt rfl rfl (by simp)

theorem BodyPost.schedule {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s n s') (hp : StepPre s) :
    Spec.TripleDes.scheduleAt s'.mem (addr32 (s.gpr .ebx)) = Spec.TripleDes.scheduleAt s.mem (addr32 (s.gpr .ebx)) := by
  apply VG.Proof.TripleDes.scheduleAt_eq_of_frame _ h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro hp.keyData
      (And.intro (hp.keyBuf.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024))) hp.stackKey.symm)

theorem BodyPost.tailData {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64) :
    Spec.TripleDes.blocksAt s'.mem (addr32 (s.gpr .esi) + 8) n = Spec.TripleDes.blocksAt s.mem (addr32 (s.gpr .esi) + 8) n := by
  have sub : Region.Sub ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ (dataR s (n + 1)) :=
    Offset.sub_base _ (by change 8 + 8 * n ≤ 8 * (n + 1); omega)
  have sep : (Region.mk (addr32 (s.gpr .esi) + 8) (8 * n)).Disjoint (dataR s) :=
    Offset.disjoint_base _ (d := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blocksAt_frame h.mem
  simpa only [stepWrites, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      (And.intro ((hp.dataBuf.sub_left sub).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
        (hp.stackData.sub_right sub).symm)

theorem firstBlock_frame {d : Spec.TripleDes.Direction} {s s' : State} {n : Nat} {m : Mem}
    (h : BodyPost d s (n + 1) s') (hp : StepPre s (n + 1)) (bound : 8 * (n + 1) ≤ 2 ^ 64)
    (frame : Frame (loopWrites s' n) s'.mem m) (hn : 1 ≤ n) :
    Spec.TripleDes.blockAt m (addr32 (s.gpr .esi)) = Spec.TripleDes.blockAt s'.mem (addr32 (s.gpr .esi)) := by
  have first : Region.Sub (dataR s) (dataR s (n + 1)) := Region.sub_prefix (by change 8 ≤ 8 * (n + 1); omega)
  have sep : (dataR s).Disjoint ⟨addr32 (s.gpr .esi) + 8, 8 * n⟩ :=
    Offset.base_disjoint _ (e := 8) (n := 8 * n) (k := 8) (by decide) (by omega)
  apply VG.Proof.TripleDes.blockAt_eq_of_frame _ frame
  have buf := h.reg .ebp (by decide) (by decide) (by decide)
  have ptrAddr : addr32 (s'.gpr .esi) = addr32 (s.gpr .esi) + 8 := by
    rw [h.ptr]
    exact addr_add (k := 8) (by omega_using [hp.dataFit, hn])
  have sp := h.reg .esp (by decide) (by decide) (by decide)
  simpa only [loopWrites, dataR, buf, ptrAddr, sp,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using
    And.intro sep
      (And.intro ((hp.dataBuf.sub_left first).sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
        (hp.stackData.sub_right first).symm)

end VG.Proof.TripleDes.X86.Ecb
