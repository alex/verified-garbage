import VerifiedGarbage.Proof.TripleDes.X86_64.Key.Loop
import VerifiedGarbage.Proof.TripleDes.Schedule

namespace VG.Proof.TripleDes.X86_64.Key

open VG VG.X86_64

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .rsp], s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 offset) 8)
    (hw : ∀ j < 16, InRegions s.wr
      (s.gpr .rdx + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8) :
    WP isa (Impl.TripleDes.X86_64.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (s.gpr .rdi + BitVec.ofNat 64 offset))))
        (s.gpr .rdx + BitVec.ofNat 64 (128 * component)) s) := by
  rw [Impl.TripleDes.X86_64.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc hr)
  intro s₁ h₁
  have writes : ∀ j < 16, InRegions s₁.wr
      (s.gpr .rdx + BitVec.ofNat 64 (128 * component) + BitVec.ofNat 64 (8 * j)) 8 := by
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

end VG.Proof.TripleDes.X86_64.Key
