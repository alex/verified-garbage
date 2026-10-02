import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-!
# Writing a batch's cached powers into the local table

Each constant field is four immediate words stored at a constant offset of
`x0`; the batch is chosen by subtracting each index from the public counter
`x19` and testing the difference for zero.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64 VG.Proof.X25519

theorem cachedFieldStore_ok {s : State} {base : Addr} (hs : Scr s base) (v : Spec.X25519.Fe)
    {dst : Nat} (ha : dst % 8 = 0) (ho : dst + 32 ≤ 8192) :
    WP isa (.block (cachedFieldStore v dst)) s fun t =>
      F t.mem base dst = v ∧ TableKeep base dst 32 s t := by
  rw [cachedFieldStore, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) ⟨ha, ho⟩) fun u hu => ?_
  subst u
  refine ⟨?_, ⟨hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩⟩
  · rw [F, fe_st4 _ _ (by omega), hv, toFe_self]
  · rw [hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem cachedPointStore_ok {s : State} {base : Addr} (hs : Scr s base) (q : Spec.Ed25519.Point)
    {dst : Nat} (ha : dst % 8 = 0) (ho : dst + 128 ≤ 8192) :
    WP isa (.block (cachedPointStore q dst)) s fun t =>
      tablePoint t.mem base dst = q ∧ TableKeep base dst 128 s t := by
  rw [cachedPointStore, WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok hs q.X ha (by omega)) fun a ⟨ax, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (ka.scratch hs) q.Y (dst := dst + 32) (by omega) (by omega))
    fun b ⟨by_, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (kb.scratch (ka.scratch hs)) q.Z (dst := dst + 64)
    (by omega) (by omega)) fun c ⟨cz, kc⟩ => ?_
  refine WP.mono (cachedFieldStore_ok (kc.scratch (kb.scratch (ka.scratch hs))) q.T
    (dst := dst + 96) (by omega) (by omega)) fun t ⟨tt, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by omega) (by omega)).trans (kb.mono (by omega) (by omega))).trans
    ((kc.mono (by omega) (by omega)).trans (kt.mono (by omega) (by omega)))⟩
  have ex : F t.mem base dst = q.X := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)),
      Outside_F kc.mem (by omega) (Or.inl (by omega)),
      Outside_F kb.mem (by omega) (Or.inl (by omega)), ax]
  have ey : F t.mem base (dst + 32) = q.Y := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)),
      Outside_F kc.mem (by omega) (Or.inl (by omega)), by_]
  have ez : F t.mem base (dst + 64) = q.Z := by
    rw [Outside_F kt.mem (by omega) (Or.inl (by omega)), cz]
  simp only [tablePoint, ex, ey, ez, tt]

end VG.Proof.Ed25519.AArch64
