import VerifiedGarbage.Impl.Ed25519.AArch64.PointEncode
import VerifiedGarbage.Proof.Ed25519.AArch64.Power
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep

/-! Untrusted: normalize extended coordinates with the verified inversion chain. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

theorem affine_eval (e : Env) :
    evalOps affineOps e 0 = e 0 * e 15 ∧ evalOps affineOps e 1 = e 1 * e 15 := ⟨rfl, rfl⟩

theorem pointAffine_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa pointAffine s fun t => CounterKeep base s t ∧
      env t.mem base 0 = env s.mem base 0 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) ∧
      env t.mem base 1 = env s.mem base 1 * Spec.X25519.pow (env s.mem base 2) (Spec.X25519.P - 2) := by
  rw [pointAffine]
  refine WP.seq (WP.mono (invert_ok hs) fun t ⟨hk, hv⟩ => ?_)
  refine WP.mono (fieldCode_ok affineOps (hk.scr hs)) fun u ⟨ku, vu⟩ => ?_
  refine ⟨⟨fun r hr hb => (ku.gpr r hr).trans (hk.gpr r hr hb), ku.rd.trans hk.rd,
    ku.wr.trans hk.wr, ku.sp.trans hk.sp,
    (hk.mem.mono (by decide) (by decide)).trans ku.mem⟩, ?_, ?_⟩
  · rw [vu, (affine_eval _).1, hv]
    have he : env t.mem base 0 = env s.mem base 0 := by
      change F t.mem base 64 = F s.mem base 64
      unfold F; rw [hk.mem.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]
  · rw [vu, (affine_eval _).2, hv]
    have he : env t.mem base 1 = env s.mem base 1 := by
      change F t.mem base 96 = F s.mem base 96
      unfold F; rw [hk.mem.fe (Or.inl (by decide)) (by decide)]
    rw [he, Proof.X25519.invert_eq]

end VG.Proof.Ed25519.AArch64
