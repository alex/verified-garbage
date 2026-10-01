import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.CTBody
import VerifiedGarbage.Proof.Ed25519.Arm.SignCached.Entry
import VerifiedGarbage.Proof.Ed25519.Arm.Whole.WrapCT

namespace VG.Proof.Ed25519.Arm.SignCached
open VG VG.Arm VG.Impl.Ed25519.Arm.SignCached

theorem lay_eq {s t : State} (hp : signCachedLocal.pub s t) : lay s = lay t := by
  obtain ⟨sp, h0, h1, h2, h3, h4, h5⟩ := hp
  simp only [lay, Whole.base, sp, h0, h1, h2, h3, h4, h5]

theorem signCached_ct :
    ConstantTime isa signCachedLocal.pre signCachedLocal.pub code := by
  refine Whole.wrap_ct (by decide) (fun _ _ hp => hp.1)
    (fun _ h => entry_below h) (fun _ h => entry_top h) (fun _ h => entry_read h) ?_ ?_
  · intro s hs p hp
    exact WP.mono (body_ok (entry_ctx hs hp) (lay_ok hs) (entry_args hs hp) (entry_key hs hp))
      fun _ _ => trivial
  · intro s t hs ht hp
    rintro a b ta tb a' b' ⟨p, q, hpa, hqb, rfl, rfl⟩ ea eb
    have he := lay_eq hp
    have hq : Ctx (lay s) t.gpr q.mem (q.withRegions (Whole.bodyRd t) (Whole.bodyWr t)) :=
      he ▸ entry_ctx ht hqb
    have hqa : Arguments (lay s) q.mem := he ▸ entry_args ht hqb
    exact ⟨(body_ct (lay_ok hs) (entry_args hs hpa) hqa _ _ _ _ _ _
      ⟨entry_ctx hs hpa, hq, trivial, trivial⟩ ea eb).1, trivial⟩

end VG.Proof.Ed25519.Arm.SignCached
