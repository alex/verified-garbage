import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Entry
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem body_depth (v : Whole.Backend) : (body v.code v.suffix).aarch64Depth ≤ 1 := by
  have hu := Whole.update_depth v
  have hf := Whole.finalize_depth v
  change (Impl.Sha512.AArch64.Stream.updateWith v.suffix v.code).aarch64Depth ≤ 1 at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.suffix v.code).aarch64Depth ≤ 1 at hf
  have hr := Whole.depth_zero_of_noFrames reduce_noFrames
  have hb := Whole.depth_zero_of_noFrames base_noFrames
  have hm := Whole.depth_zero_of_noFrames mul_noFrames
  simp only [body, secretCode, nonceCode, challengeCode, hashSeed, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.AArch64.Whole.callWith, Code.aarch64Depth,
    Impl.Sha512.AArch64.Stream.init, hr, hb, hm]
  omega

theorem signCached_ok (v : Whole.Backend) {s : State} (h : signCachedLocal.pre s) :
    WP isa (code v.code v.suffix) s fun u => abiPreserved s u ∧ signCachedLocal.post s u := by
  have hw := Whole.wrap_ok (body_depth v) (entry_below h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (s.gpr .x0) 64 = Spec.Ed25519.sign
      (Spec.Ed25519.bytesAt m (s.gpr .x1) 32)
      (Spec.Ed25519.bytesAt m (s.gpr .x3) (s.gpr .x4).toNat))
    (fun p hp => WP.mono (body_ok v (entry_ctx h hp) (lay_ok h) (entry_args hp) (entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        simpa only [Whole.bodyRd, h.1, Ctx, Lay.inputs, Lay.outputs, Lay.SEED, Lay.PK, Lay.MSG,
          Lay.OUT, Lay.SCR, Lay.ARGS, Whole.ARGS, show BitVec.ofNat 64 256 = (256 : Addr) from rfl, lay, h.2.1, List.cons_append, List.nil_append] using hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs := entry_input h hf (r := ⟨s.gpr .x1, 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hm := entry_input h hf (r := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩) (by rw [h.1]; simp)
    (Nat.le_of_lt (s.gpr .x4).isLt)
  change Spec.Ed25519.bytesAt u.mem (s.gpr .x0) 64 = _
  rw [hp, hs, hm]

end VG.Proof.Ed25519.AArch64.SignCached
