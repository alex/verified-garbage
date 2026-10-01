import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Hash
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Base
import VerifiedGarbage.Proof.Ed25519.AArch64.PublicKey.Entry

namespace VG.Proof.Ed25519.AArch64.PublicKey
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.PublicKey

variable {L : Lay} {g : Reg → Addr} {vec : VReg → BitVec 128} {m₀ : Mem} {t : State}

theorem body_ok (v : Whole.Backend) (hc : Ctx L g vec m₀ t) (hL : L.Ok) (ha : Arguments L m₀) :
    WP isa (body v.code v.suffix) t fun u => Ctx L g vec m₀ u ∧
      Spec.Ed25519.bytesAt u.mem L.out 32 = Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m₀ L.seed 32) := by
  refine WP.seq (WP.mono (hash_ok v hc hL ha) fun u ⟨hu, hh⟩ => ?_)
  refine WP.seq (WP.mono (prune_step hu hh) fun u' ⟨hu', hs⟩ => ?_)
  refine WP.seq (WP.mono (base_step hu' hL ha hs) fun u'' ⟨hu'', hp⟩ => ?_)
  exact WP.mono (wipe_step hu'' hL) fun w ⟨hw, hm⟩ => ⟨hw, hm.trans hp⟩

theorem body_noFrames (v : Whole.Backend) : (body v.code v.suffix).noFrames = true := by
  have hu := Whole.update_noFrames v
  have hf := Whole.finalize_noFrames v
  change (Impl.Sha512.AArch64.Stream.updateWith v.code).noFrames = true at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.code).noFrames = true at hf
  simp only [body, Impl.Ed25519.AArch64.PublicKey.hash, Impl.Ed25519.AArch64.Whole.callWith, Code.noFrames,
    Impl.Sha512.AArch64.Stream.init, hu, hf, Bool.and_self]
  rw [base_noFrames]
  rfl

theorem publicKey_ok (v : Whole.Backend) {s : State} (h : pkLocal.pre s) :
    WP isa (code v.code v.suffix) s fun u => abiPreserved s u ∧ pkLocal.post s u := by
  have hw := Whole.wrap_ok (body_noFrames v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 32 =
      Spec.Ed25519.publicKey (Spec.Ed25519.bytesAt m (s.gpr .x1) 32))
    (fun p hp => WP.mono (body_ok v (entry_ctx h hp) (lay_ok h) (entry_args hp)) fun u ⟨hu, ho⟩ => ⟨by
      simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.OUT,
        Lay.SCR, Lay.ARGS, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs : Spec.Ed25519.bytesAt m (s.gpr .x1) 32 = Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 32 := by
    unfold Spec.Ed25519.bytesAt
    refine List.map_congr_left fun i hi => hf.bytes (R := ⟨s.gpr .x1, 32⟩) ?_
      (by change 32 ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
    rintro r hr
    rw [List.mem_singleton.mp hr]
    exact (lay_ok h).ks.symm
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 32 = _
  rw [hp, hs]

end VG.Proof.Ed25519.AArch64.PublicKey
