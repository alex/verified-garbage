import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.CTBody
import VerifiedGarbage.Proof.Ed25519.AArch64.SignCached.Correct
import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.WrapCT

namespace VG.Proof.Ed25519.AArch64.SignCached
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.SignCached

theorem lay_eq {s t : State} (hp : signCachedLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, h4, h5]

theorem signCached_ct (v : Whole.Backend) :
    ConstantTime isa signCachedLocal.pre signCachedLocal.pub (code v.code v.suffix) := by
  refine Whole.wrap_ct (fun _ _ hp => hp.1) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok v (entry_ctx hs hp) (lay_ok hs) (entry_args hp) (entry_key hs hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr t.v q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args hqb
    exact ⟨(body_ct v (lay_ok hs) (entry_args hpa) hqa _ _ _ _ _ _
      ⟨entry_ctx hs hpa, hq, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.AArch64.SignCached
