import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Body
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Entry
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTReady

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem body_noFrames : body.noFrames = true := by
  simp only [body, secretCode, nonceCode, challengeCode, hashSeed, hashNonce, hashChallenge,
    init, update, finalize, reduce, Impl.Ed25519.Arm.Whole.callWith, Code.noFrames,
    Impl.Sha512.Arm.Stream.init, Bool.and_self]
  rw [reduce_noFrames, base_noFrames, mul_noFrames]
  rfl

theorem signCached_ok {s : State} (h : signCachedLocal.pre s) :
    WP isa code s fun u => abiPreserved s u ∧ signCachedLocal.post s u := by
  have hw := Whole.wrap_ok body_noFrames (by decide : 6 ≤ 6) (entry_below h) (entry_top h) (entry_read h) (entry_writes h)
    (P := fun m m' _ => Spec.Ed25519.bytesAt m' (State.addr (s.gpr .r0)) 64 = Spec.Ed25519.sign
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r1)) 32)
      (Spec.Ed25519.bytesAt m (State.addr (s.gpr .r3)) (stackArg s 0).toNat))
    (fun p hp => WP.mono (body_ok (entry_ctx h hp) (lay_ok h) (entry_args h hp) (entry_key h hp))
      fun u ⟨hu, ho⟩ => ⟨by
        change Whole.Ctx (Whole.base s) s.gpr p.mem (lay s).inputs (lay s).outputs u at hu
        rw [(entry_regions h).1, (entry_regions h).2] at hu
        exact hu, ho⟩)
  refine WP.mono hw fun u ⟨hu, m, hf, hp⟩ => ⟨hu, ?_⟩
  have hs := entry_input h hf (r := ⟨State.addr (s.gpr .r1), 32⟩) (by rw [h.1]; simp) (by change 32 ≤ 2 ^ 64; decide)
  have hm := entry_input h hf (r := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩) (by rw [h.1]; simp)
    (by have := (stackArg s 0).isLt; change (stackArg s 0).toNat ≤ 2 ^ 64; omega)
  change Spec.Ed25519.bytesAt u.mem (State.addr (s.gpr .r0)) 64 = _
  rw [hp, hs, hm]

end VG.Proof.Ed25519.Arm.SignCached
