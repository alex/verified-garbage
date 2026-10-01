import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Body
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Entry
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTReady

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem body_noFrames (v : Whole.Backend) : (body v.code v.suffix).noFrames = true := by
  have hu := Whole.update_noFrames v
  have hf := Whole.finalize_noFrames v
  change (Impl.Sha512.AArch64.Stream.updateWith v.code).noFrames = true at hu
  change (Impl.Sha512.AArch64.Stream.finalizeWith v.code).noFrames = true at hf
  simp only [body, secretCode, nonceCode, challengeCode, hashSeed, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.AArch64.Whole.callWith, Code.noFrames,
    Impl.Sha512.AArch64.Stream.init, hu, hf, Bool.and_self]
  rw [reduce_noFrames, base_noFrames, mul_noFrames]
  rfl

theorem signCached_ok (v : Whole.Backend) {s : State} (h : signCachedLocal.pre s) :
    WP isa (code v.code v.suffix) s fun u => abiPreserved s u ∧ signCachedLocal.post s u := by
  have hw := Whole.wrap_ok (body_noFrames v) (entry_below h) (entry_writes h)
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
