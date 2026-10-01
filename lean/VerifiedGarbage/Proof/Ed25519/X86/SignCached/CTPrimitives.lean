import VerifiedGarbage.Proof.Ed25519.X86.SignCached.CTCommon
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Body

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.Whole
open VG.Impl.Ed25519.X86.SignCached

variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem reduce_call_ct (hL : L.Ok) (d : Nat) (hd : 24 ≤ d) (hd' : d + 32 ≤ 256) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.frame d, .frame 192, .caller 5 0]))
      (.call "vg_ed25519_scalar_reduce" Impl.Ed25519.X86.scalarReduce)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarReduce_ok scalarReduce_ct Whole.reduce_nosp (by rw [Whole.reduce_stack]; decide)
  · intro g m t hc hs
    exact reduce_ready hc hL hd hd' (hs.slot hL (j := 0) (by simp) (by simp))
      (hs.slot hL (j := 1) (by simp) (by simp))
      ((hs.slot hL (j := 2) (by simp) (by simp)).trans (BitVec.add_zero _))
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by simp) h (by decide : 0 < 3),
      call_args_eq hL (by simp) h (by decide : 1 < 3), call_args_eq hL (by simp) h (by decide : 2 < 3)⟩

theorem base_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 0, .frame 96, .caller 5 0]))
      (.call "vg_ed25519_scalar_base" Impl.Ed25519.X86.scalarBase)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarBase_ok scalarBase_ct base_nosp (by rw [base_stack]; decide)
  · intro g m t hc hs
    exact base_ready hc hL ⟨((hs.slot hL (j := 0) (by decide) (by decide)).trans (BitVec.add_zero _)),
      hs.slot hL (j := 1) (by decide) (by decide),
      ((hs.slot hL (j := 2) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 3),
      call_args_eq hL (by decide) h (by decide : 1 < 3), call_args_eq hL (by decide) h (by decide : 2 < 3)⟩

theorem mul_call_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ (OutArgs L [.caller 0 32, .frame 96, .frame 128, .frame 32, .caller 5 0]))
      (.call "vg_ed25519_scalar_mul_add" Impl.Ed25519.X86.scalarMulAdd)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  apply call_ct hL scalarMulAdd_ok scalarMulAdd_ct mul_nosp (by rw [mul_stack]; decide)
  · intro g m t hc hs
    exact mul_ready hc hL ⟨hs.slot hL (j := 0) (by decide) (by decide),
      hs.slot hL (j := 1) (by decide) (by decide), hs.slot hL (j := 2) (by decide) (by decide),
      hs.slot hL (j := 3) (by decide) (by decide),
      ((hs.slot hL (j := 4) (by decide) (by decide)).trans (BitVec.add_zero _))⟩
  · intro a b ar aw br bw h
    exact ⟨congrArg (· - 4) (two_esp h), call_args_eq hL (by decide) h (by decide : 0 < 5),
      call_args_eq hL (by decide) h (by decide : 1 < 5), call_args_eq hL (by decide) h (by decide : 2 < 5),
      call_args_eq hL (by decide) h (by decide : 3 < 5), call_args_eq hL (by decide) h (by decide : 4 < 5)⟩

theorem saveSecret_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp (Whole.block_rel (fun _ _ h => two_esp h) (by taint_decide)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.X86.SignCached
