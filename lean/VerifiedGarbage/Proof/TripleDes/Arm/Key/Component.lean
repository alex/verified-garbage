import VerifiedGarbage.Proof.TripleDes.Arm.Key.Loop
import VerifiedGarbage.Proof.TripleDes.Schedule

namespace VG.Proof.TripleDes.Arm.Key

open VG VG.Arm
open VG.Proof.TripleDes.Arm.Key (keyKept)

structure ComponentPost (keys : Spec.TripleDes.DesSchedule) (base : Addr) (s s' : State) : Prop where
  keys : ∀ i < 16, s'.mem.readW (base + BitVec.ofNat 64 (8 * i)) 64 = (keys.getD i 0).setWidth 64
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  reg : ∀ r ∈ keyKept, s'.gpr r = s.gpr r
  frame : Frame [⟨base, 128⟩] s.mem s'.mem

theorem component_ok (s : State) (offset component : Nat) (hc : component < 3)
    (ho : offset + 4 < 4096)
    (keyFit : (s.gpr .r0).toNat + offset + 8 ≤ 2 ^ 32)
    (scheduleFit : (s.gpr .r2).toNat + 384 ≤ 2 ^ 32)
    (hr : ∀ t < 2, InRegions (s.rd ++ s.wr)
      (State.addr (s.gpr .r0 + BitVec.ofNat 32 (offset + 4 * t))) 4)
    (hw : ∀ j < 16, ∀ t < 2, InRegions s.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * component) +
        BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4) :
    WP isa (Impl.TripleDes.Arm.Key.component offset component) s
      (ComponentPost (Spec.TripleDes.expandDesKey (Spec.TripleDes.decodeBlock
        (Spec.TripleDes.blockAt s.mem (State.addr (s.gpr .r0 + BitVec.ofNat 32 offset)))))
        (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * component))) s) := by
  rw [Impl.TripleDes.Arm.Key.component]
  apply WP.seq
  apply WP.mono (load_ok s offset component hc ho keyFit hr)
  intro s₁ h₁
  have writes : ∀ j < 16, ∀ t < 2, InRegions s₁.wr
      (State.addr (s.gpr .r2 + BitVec.ofNat 32 (128 * component) +
        BitVec.ofNat 32 (8 * j) + BitVec.ofNat 32 (4 * t))) 4 := by
    rw [h₁.wr]; exact hw
  have fit : (s.gpr .r2 + BitVec.ofNat 32 (128 * component)).toNat + 128 ≤ 2 ^ 32 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega_using [hc] : 128 * component < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega_using [scheduleFit, hc] : (s.gpr .r2).toNat + 128 * component < 2 ^ 32)]
    omega_using [scheduleFit, hc]
  apply WP.mono (loop_ok _ _ s₁ fit writes h₁.c h₁.d h₁.counter h₁.ptr)
  intro s₂ h₂
  refine ⟨?_, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr,
    fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), ?_⟩
  · intro i hi
    rw [VG.Proof.TripleDes.expandDesKey_prefix, VG.Proof.TripleDes.vector_getD _ i hi 0]
    exact h₂.keys i hi hi
  · rw [← h₁.mem]
    exact h₂.frame

end VG.Proof.TripleDes.Arm.Key
