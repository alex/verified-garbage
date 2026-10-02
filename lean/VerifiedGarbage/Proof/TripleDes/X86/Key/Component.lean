import VerifiedGarbage.Proof.TripleDes.X86.Key.Loop
import VerifiedGarbage.Proof.TripleDes.Schedule

namespace VG.Proof.TripleDes.X86.Key
open VG VG.X86 VG.X86.Straight
open VG.Proof.Rc2.X86 (addr32)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : BitVec 32) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (addr32 base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  bp : s'.gpr .ebp = s.gpr .ebp
  sp : s'.gpr .esp = s.gpr .esp
  frame : Frame [scheduleRegion base, workRegion s] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hok : Ok sboxCfg s)
    (keyFit : (keyArg s).toNat + offset + 8 ≤ 2 ^ 32)
    (scheduleFit : (scheduleArg s + BitVec.ofNat 32 (128 * component)).toNat + 128 ≤ 2 ^ 32)
    (harg : ∀ i ∈ [1, 3], InRegions (s.rd ++ s.wr) (wordAddr (s.gpr .esp) i) 4)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr) (keyAddr s (offset + 4 * t)) 4)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4)
    (hdis : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s)) :
    WP isa (Impl.TripleDes.X86.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (keyAddr s offset))))
        (scheduleArg s + BitVec.ofNat 32 (128 * component)) s) := by
  rw [Impl.TripleDes.X86.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hok keyFit harg hr)
  intro s₁ h₁
  have hok₁ : Ok sboxCfg s₁ := hok.congr h₁.base h₁.base h₁.rd h₁.wr
  have writes : ∀ j < 16, ∀ t < 2, InRegions s₁.wr
      (addr32 (scheduleArg s + BitVec.ofNat 32 (128 * component)) + BitVec.ofNat 64 (8 * j + 4 * t)) 4 := by
    rw [h₁.wr]; exact hw
  have work₁ : workRegion s₁ = workRegion s := by unfold workRegion; rw [h₁.base]
  have dis₁ : (scheduleRegion (scheduleArg s + BitVec.ofNat 32 (128 * component))).Disjoint (workRegion s₁) := by
    rw [work₁]; exact hdis
  apply WP.mono (loop_ok _ _ s₁ scheduleFit hok₁ writes dis₁ h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₂.bp.trans h₁.base,
    h₂.sp.trans h₁.sp, ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · have hf := h₂.frame
    rw [work₁] at hf
    exact (h₁.frame.mono (by intro r hr; obtain rfl := List.mem_singleton.mp hr; simp)).trans hf

end VG.Proof.TripleDes.X86.Key
