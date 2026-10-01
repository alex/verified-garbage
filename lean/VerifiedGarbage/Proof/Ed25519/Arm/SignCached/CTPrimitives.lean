import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTReady

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.Whole VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : d + 32 ≤ 184) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .frame d), (.r1, .frame 184), (.r2, .caller 5 0)] []))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.Arm.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct reduce_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .frame d) (by simp)
    have a1 := hs.1 (.r1, .frame 184) (by simp)
    have a2 := hs.1 (.r2, .caller 5 0) (by simp)
    change t.gpr .r2 = L.scr + 0#32 at a2
    rw [BitVec.add_zero] at a2
    exact reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .frame d)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r1, .frame 184)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .caller 5 0)) h (by simp) (by simp [linkRegs])⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 0 0), (.r1, .frame 88), (.r2, .caller 5 0)] []))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.Arm.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarBase_ok scalarBase_ct base_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 0 0) (by simp)
    change t.gpr .r0 = L.out + 0#32 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs.1 (.r1, .frame 88) (by simp)
    have a2 := hs.1 (.r2, .caller 5 0) (by simp)
    change t.gpr .r2 = L.scr + 0#32 at a2
    rw [BitVec.add_zero] at a2
    exact base_ready hL ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 0 0)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r1, .frame 88)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .caller 5 0)) h (by simp) (by simp [linkRegs])⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (AllArgs L [(.r0, .caller 0 32), (.r1, .frame 88), (.r2, .frame 120), (.r3, .frame 24)] [.caller 5 0]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.Arm.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarMulAdd_ok scalarMulAdd_ct mul_noFrames
  · intro g m t hc hs
    have a0 := hs.1 (.r0, .caller 0 32) (by simp)
    have a1 := hs.1 (.r1, .frame 88) (by simp)
    have a2 := hs.1 (.r2, .frame 120) (by simp)
    have a3 := hs.1 (.r3, .frame 24) (by simp)
    have a4 := hs.2 0 (by decide)
    change stackArg t 0 = L.scr + 0#32 at a4
    rw [BitVec.add_zero] at a4
    exact mul_ready hc hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.r0, .caller 0 32)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r1, .frame 88)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r2, .frame 120)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.r3, .frame 24)) h (by simp) (by simp [linkRegs]),
      stack_eq h (j := 0) (by decide)⟩

end VG.Proof.Ed25519.Arm.SignCached
