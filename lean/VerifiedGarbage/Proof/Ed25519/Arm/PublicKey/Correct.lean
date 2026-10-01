import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Hash
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Base
import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Entry

namespace VG.Proof.Ed25519.Arm.PublicKey
open VG VG.Arm VG.Impl.Ed25519.Arm.PublicKey

variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem} {t : State}

theorem body_ok (hc : Ctx L g m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa body t fun u => Ctx L g m₀ u ∧
      Spec.Ed25519.bytesAt u.mem (State.addr L.out) 32 =
        Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ (State.addr L.seed) 32) := by
  refine WP.seq (WP.mono (hash_ok hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step hu hL hh) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (base_step hu' hL ha hs) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_noFrames : body.noFrames = true := by
  simp only [body, Impl.Ed25519.Arm.PublicKey.hash, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames,
    Impl.Sha512.Arm.Stream.init, Bool.and_self]
  rw [base_noFrames]
  rfl

theorem publicKey_ok {s : State} (h : pkLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 3 ≤ 6) (entry_below h)
    (by simp only [Nat.reduceSub, Nat.mul_zero, Nat.add_zero]; exact Nat.le_of_lt s.sp.isLt)
    (by intro j hj h4; omega) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32))
    (fun p hp => WP.mono (body_ok (entry_ctx h hp) (lay_ok h) (entry_args (entry_below h) hp))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
          Lay.SCR, Lay.ARGS, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32 =
      Spec.Ed25519.bytesAt s.mem (State.addr (s.gpr .r1)) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨State.addr (s.gpr .r1), 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 32 = _
  rw [hp, hs]

end VG.Proof.Ed25519.Arm.PublicKey
