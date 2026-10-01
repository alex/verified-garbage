import VerifiedGarbage.Proof.TripleDes.AArch64.Key.Loop
import VerifiedGarbage.Proof.TripleDes.Schedule

namespace VG.Proof.TripleDes.AArch64.Key

open VG VG.AArch64
open VG.Proof.TripleDes.AArch64.Key (keyKept)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset % 8 = 0 ∧ offset < 32768)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.AArch64.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .x0 + BitVec.ofNat 64 offset))))
        (s.gpr .x2 + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.AArch64.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc ho hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .x2 + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
    rw [h₁.wr]; exact hw
  apply WP.mono (loop_ok _ _ s₁ writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.AArch64.Key
