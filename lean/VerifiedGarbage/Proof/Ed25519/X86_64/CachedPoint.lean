import VerifiedGarbage.Impl.Ed25519.X86_64.Cached
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop

/-!
# Cached points

The cached addition is the specification's `pointAdd` (`grind`); each constant
field of a cached point is four immediate words stored through `rax`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off F Keeps Outside fe_st4 st4_outside)

variable {fld : Arith} [EdArith fld]

def addCachedResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 * e 7
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddCached_formula (e : Env) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = addCachedResult e := rfl

theorem pointAddCached_eval (e : Env) (q : Spec.Ed25519.Point) (hq : point e 4 5 6 7 = cache q) :
    point (evalOps pointAddCachedOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  have h7 : e 7 = q.Z * 2 := congrArg Spec.Ed25519.Point.T hq
  rw [pointAddCached_formula]
  simp only [addCachedResult, point, Spec.Ed25519.pointAdd, h4, h5, h6, h7]
  congr 1 <;> grind

theorem pointAddCached_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointAddCachedOps e i = e i :=
  point_ops_high _ (by decide) e i hi

theorem pointAddCachedWide_ok {s : State} {base : Addr} (hs : Scratch s base)
    (q : Spec.Ed25519.Point) (hq : point (env s.mem base) 4 5 6 7 = cache q) :
    WP isa (.block (pointAddCached fld)) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCodeWide_ok hs pointAddCachedOps) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointAddCached_eval _ q hq, pointAddCached_high _⟩

theorem cachedFieldStore_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (v : Spec.X25519.Fe) (dst : Nat) (ho : o + dst + 32 ≤ 8192) :
    WP isa (.block (cachedFieldStore v dst)) s fun t =>
      F t.mem base (o + dst) = v ∧ TableKeep base (o + dst) 32 s t := by
  rw [cachedFieldStore, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (tableWords_ok (hs.of_keeps hk (by decide)) ((hk.1 _ (by decide)).trans hp) dst ho)
    fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  refine ⟨?_, ⟨fun r hr => (congrFun hg r).trans (hk.1 r hr), hrd.trans hk.2.2.1,
    hwr.trans hk.2.2.2, ?_⟩⟩
  · rw [F, hm, fe_st4 _ _ (by omega), hv, Proof.X25519.toFe_self]
  · rw [hm, hk.2.1]; exact st4_outside _ _ (by omega) _ _ _ _

theorem cachedPointStore_ok {s : State} {base : Addr} (hs : Scratch s base) {o : Nat}
    (hp : s.gpr .rax = off base o) (q : Spec.Ed25519.Point) (dst : Nat) (ho : o + dst + 128 ≤ 8192) :
    WP isa (.block (cachedPointStore q dst)) s fun t =>
      tablePoint t.mem base (o + dst) = q ∧ TableKeep base (o + dst) 128 s t := by
  rw [cachedPointStore, WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok hs hp q.X dst (by omega)) fun a ⟨ax, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (ka.scratch hs) ((ka.gpr _ (by decide)).trans hp) q.Y (dst + 32)
    (by omega)) fun b ⟨by_, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (cachedFieldStore_ok (kb.scratch (ka.scratch hs))
    ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hp)) q.Z (dst + 64)
    (by omega)) fun c ⟨cz, kc⟩ => ?_
  refine WP.mono (cachedFieldStore_ok (kc.scratch (kb.scratch (ka.scratch hs)))
    ((kc.gpr _ (by decide)).trans ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hp)))
    q.T (dst + 96) (by omega)) fun t ⟨tt, kt⟩ => ?_
  refine ⟨?_, ((ka.mono (by omega) (by omega)).trans (kb.mono (by omega) (by omega))).trans
    ((kc.mono (by omega) (by omega)).trans (kt.mono (by omega) (by omega)))⟩
  have ex : F t.mem base (o + dst) = q.X := by
    rw [Outside_F (d := o + dst) kt.mem (by omega) (Or.inl (by omega)),
      Outside_F (d := o + dst) kc.mem (by omega) (Or.inl (by omega)),
      Outside_F (d := o + dst) kb.mem (by omega) (Or.inl (by omega)), ax]
  have ey : F t.mem base (o + dst + 32) = q.Y := by
    rw [show o + dst + 32 = o + (dst + 32) by omega,
      Outside_F (d := o + (dst + 32)) kt.mem (by omega) (Or.inl (by omega)),
      Outside_F (d := o + (dst + 32)) kc.mem (by omega) (Or.inl (by omega)), by_]
  have ez : F t.mem base (o + dst + 64) = q.Z := by
    rw [show o + dst + 64 = o + (dst + 64) by omega,
      Outside_F (d := o + (dst + 64)) kt.mem (by omega) (Or.inl (by omega)), cz]
  have et : F t.mem base (o + dst + 96) = q.T := by
    rw [show o + dst + 96 = o + (dst + 96) by omega, tt]
  simp only [tablePoint, ex, ey, ez, et]

end VG.Proof.Ed25519.X86_64
