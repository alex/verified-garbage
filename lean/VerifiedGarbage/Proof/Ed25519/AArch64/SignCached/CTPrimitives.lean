import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole VG.Impl.Ed25519.AArch64.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 64} {v₁ v₂ : VReg → BitVec 128} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .frame d), (.x1, .frame 192), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.AArch64.scalarReduce)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarReduce_ok scalarReduce_ct (Whole.depth_of_noFrames reduce_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .frame d) (by simp)
    have a1 := hs (.x1, .frame 192) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact reduce_ready hL hd ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .frame d)) h (by simp) (by simp [linkRegs]),
      call_gpr_eq (p := (.x1, .frame 192)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 0), (.x1, .frame 96), (.x2, .caller 5 0)]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.AArch64.scalarBase)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarBase_ok scalarBase_ct (Whole.depth_of_noFrames base_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 0 0) (by simp)
    change t.gpr .x0 = L.out + 0#64 at a0
    rw [BitVec.add_zero] at a0
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .caller 5 0) (by simp)
    change t.gpr .x2 = L.scr + 0#64 at a2
    rw [BitVec.add_zero] at a2
    exact base_ready hL ⟨a0, a1, a2⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 0)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .caller 5 0)) h (by simp) (by decide)⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ (OutArgs L [(.x0, .caller 0 32), (.x1, .frame 96), (.x2, .frame 128), (.x3, .frame 32), (.x4, .caller 5 0)]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.AArch64.scalarMulAdd)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  apply call_ct scalarMulAdd_ok scalarMulAdd_ct (Whole.depth_of_noFrames mul_noFrames)
  · intro g v m t _ hs
    have a0 := hs (.x0, .caller 0 32) (by simp)
    have a1 := hs (.x1, .frame 96) (by simp)
    have a2 := hs (.x2, .frame 128) (by simp)
    have a3 := hs (.x3, .frame 32) (by simp)
    have a4 := hs (.x4, .caller 5 0) (by simp)
    change t.gpr .x4 = L.scr + 0#64 at a4
    rw [BitVec.add_zero] at a4
    exact mul_ready hL ⟨a0, a1, a2, a3, a4⟩
  · intro a b ar aw br bw h
    have hsp := two_sp h
    exact ⟨hsp, call_gpr_eq (p := (.x0, .caller 0 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x1, .frame 96)) h (by simp) (by decide),
      call_gpr_eq (p := (.x2, .frame 128)) h (by simp) (by decide),
      call_gpr_eq (p := (.x3, .frame 32)) h (by simp) (by decide),
      call_gpr_eq (p := (.x4, .caller 5 0)) h (by simp) (by decide)⟩

theorem saveSecret_ct :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ v₁ v₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_sp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
