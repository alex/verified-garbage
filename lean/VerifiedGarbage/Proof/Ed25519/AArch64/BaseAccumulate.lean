import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.AArch64.PointAccumulateLoop

/-!
# Adding cached points

The cached addition is the specification's `pointAdd` (`ring`); a table's
cached point is loaded straight into slots 4–7.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Fin.CommRing

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
  congr 1 <;> ring

theorem pointAddCached_high (e : Env) (i : Slot) (hi : 16 ≤ i.val) :
    evalOps pointAddCachedOps e i = e i :=
  point_ops_high _ (by decide) e i hi

theorem pointAddCached_ok {s : State} {base : Addr} (hs : Scr s base)
    (q : Spec.Ed25519.Point) (hq : point (env s.mem base) 4 5 6 7 = cache q) :
    WP isa (.block pointAddCached) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok pointAddCachedOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointAddCached_eval _ q hq, pointAddCached_high _⟩

theorem fromTableQuarterQ_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (j : Nat) (hj : j < 4) (ho : o + 128 ≤ 8192) :
    WP isa (.block (fromTableWords (32 * j) ++ stores (192 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j) ∧
      TableKeep base (192 + 32 * j) 32 s t := by
  have _hcap : workSize true = 8192 := rfl
  rw [WP.block_append_iff]
  refine WP.mono (fromTableWords_ok hs hp (32 * j) (by omega) (by omega)) fun t ⟨hv, hk⟩ => ?_
  have ht := hs.of_keeps hk (by decide)
  refine WP.mono (stores_ok ht (by constructor <;> omega) .x4 .x5 .x6 .x7) fun u hu => ?_
  subst u
  refine ⟨?_, ⟨hk.gpr, hk.rd, hk.wr, hk.sp, ?_⟩⟩
  · change F (st4 _ _ _ _ _ _ _) base (64 + 32 * (4 + j)) = _
    rw [show 64 + 32 * (4 + j) = 192 + 32 * j by omega, F, fe_st4 _ _ (by omega), hv]
  · rw [hk.mem]; exact st4_outside _ _ (by omega) _ _ _ _

theorem fromTablePrefixQ_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192)
    (n : Nat) (hn : n ≤ 4) :
    WP isa (.block ((List.range n).flatMap fun j =>
      fromTableWords (32 * j) ++ stores (192 + 32 * j) .x4 .x5 .x6 .x7)) s fun t =>
      (∀ j (hj : j < n), env t.mem base ⟨4 + j, by omega⟩ = F s.mem base (o + 32 * j)) ∧
      TableKeep base 192 (32 * n) s t := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨fun j hj => by omega,
      ⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs hp (by omega)) fun t ⟨hv, hk⟩ => ?_
    refine WP.mono (fromTableQuarterQ_ok (hk.scratch hs)
      ((hk.gpr _ (by decide)).trans hp) n (by omega) ho) fun u ⟨hu, ku⟩ => ?_
    refine ⟨fun j hj => ?_, (hk.mono (by omega) (by omega)).trans
      (ku.mono (by omega) (by omega))⟩
    by_cases h : j < n
    · have he : env u.mem base ⟨4 + j, by omega⟩ = env t.mem base ⟨4 + j, by omega⟩ :=
        Outside_F ku.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
      rw [he, hv j h]
    · have he : j = n := by omega
      subst j
      rw [hu, Outside_F hk.mem (by omega) (Or.inr (by omega))]

theorem pointFromTableQ_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat}
    (hp : s.gpr .x8 = off base o) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block pointFromTableQ) s fun t =>
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base o ∧ TableKeep base 192 128 s t := by
  refine WP.mono (fromTablePrefixQ_ok hs hp hlo ho 4 (by decide)) fun t ⟨hv, hk⟩ => ?_
  refine ⟨?_, hk⟩
  have h0 := hv 0 (by decide)
  have h1 := hv 1 (by decide)
  have h2 := hv 2 (by decide)
  have h3 := hv 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  change env t.mem base 4 = _ at h0
  change env t.mem base 5 = _ at h1
  change env t.mem base 6 = _ at h2
  change env t.mem base 7 = _ at h3
  simp only [tablePoint, point, h0, h1, h2, h3]

theorem Keep.of_tableQ {base : Addr} {s t : State}
    (h : TableKeep base 192 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm

theorem tableQ_other {base : Addr} {s t : State} (h : TableKeep base 192 128 s t)
    (i : Slot) (hi : i.val < 4 ∨ 8 ≤ i.val) : env t.mem base i = env s.mem base i := by
  change F t.mem base (offset i) = F s.mem base (offset i)
  rcases hi with hi | hi
  · exact Outside_F h.mem (by simp only [offset]; omega) (Or.inl (by simp only [offset]; omega))
  · exact Outside_F h.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

end VG.Proof.Ed25519.AArch64
