import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTCommon
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.PruneCT

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached
variable {L : Lay} {g₁ g₂ : Reg → BitVec 32} {m₁ m₂ : Mem}

theorem copyWord_ct (k : Nat) :
    RelCT isa (fun a b => a.sp = b.sp) (.block (copyWord k)) (fun a b => a.sp = b.sp) :=
  Whole.step_sp_ct (fun _ _ h => by simp only [addrs,h]) (Whole.frame_store_ct 0 (56+4*k) .r0)

theorem copyPrefix_ct :
    RelCT isa (fun a b => a.sp = b.sp) (.block copyPrefix) (fun a b => a.sp = b.sp) :=
  Whole.flatMap_sp_ct _ _ (fun _ _ => copyWord_ct _)

theorem saveSecret_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block saveSecret)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  have ct := Whole.block_append_ct PublicKey.prune_sp_ct copyPrefix_ct
  refine two_wp (ct.mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (saveSecret_ok hc hL rfl) fun _ h => ⟨h.1, trivial⟩

theorem wipe_ct (hL : L.Ok) :
    RelCT isa (Two L g₁ g₂ m₁ m₂ fun _ => True) (.block wipe)
      (Two L g₁ g₂ m₁ m₂ fun _ => True) := by
  refine two_wp ((Whole.zeroWords_ct 6 56).mono (fun _ _ h => two_sp h) (fun _ _ _ => True.intro)) ?_ ?_
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩
  · intro t hc _
    exact WP.mono (wipe_ok hc hL) fun _ h => ⟨h.1, trivial⟩

end VG.Proof.Ed25519.Arm.SignCached
