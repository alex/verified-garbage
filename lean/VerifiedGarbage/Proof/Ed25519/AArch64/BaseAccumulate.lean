import VerifiedGarbage.Impl.Ed25519.AArch64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.AArch64.PointAccumulateLoop

/-!
# Adding cached powers, sixteen scalar bits at a time

Untrusted. The cached addition is the specification's `pointAdd` (`ring`),
and the loop over a batch's sixteen bits is `accumulateLoop_ok`'s, with the
local table holding cached powers, loaded straight into slots 4–7.
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

theorem prepareCached_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hj : j < 16) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block prepareCached) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base (5376 + 128 * j) ∧
      point (env t.mem base) 17 18 19 20 = point (env s.mem base) 0 1 2 3 := by
  rw [prepareCached, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok savePointOps hs) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.scr hs).x0 5376 j (by omega)
    ((ka.gpr _ (by decide)).trans hc)) fun b ⟨pb, kb⟩ => ?_
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  refine WP.mono (pointFromTableQ_ok ((ka.trans kbe).scr hs) pb (by omega) (by omega))
    fun t ⟨pt, kt⟩ => ?_
  have o := tableQ_other kt
  refine ⟨(ka.trans kbe).trans (Keep.of_tableQ kt), ?_, ?_, ?_⟩
  · have h : point (env t.mem base) 0 1 2 3 = point (env a.mem base) 0 1 2 3 := by
      simp only [point, o 0 (by decide), o 1 (by decide), o 2 (by decide), o 3 (by decide), kb.mem]
    rw [h, va]; rfl
  · rw [pt, kb.mem]
    exact workspace_tablePoint ka.mem (by omega) (by omega)
  · have h : point (env t.mem base) 17 18 19 20 = point (env a.mem base) 17 18 19 20 := by
      simp only [point, o 17 (by decide), o 18 (by decide), o 19 (by decide), o 20 (by decide), kb.mem]
    rw [h, va, savePoint_eval]

theorem baseAccumulate_ok {s : State} {base : Addr} (hs : Scr s base)
    (j start bit : Nat) (q : Spec.Ed25519.Point) (hj : j < 16) (hi : start + j < 512) (hbit : bit < 2)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit)
    (hq : tablePoint s.mem base (5376 + 128 * j) = cache q) :
    WP isa (.block baseAccumulate) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 =
        (if bit = 0 then point (env s.mem base) 0 1 2 3 else
          Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) := by
  rw [baseAccumulate, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (prepareCached_ok hs j hj hc) fun a ⟨ka, ap, aq, av⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointAddCached_ok (ka.scr hs) q (aq.trans hq)) fun b ⟨kb, bp, bh⟩ => ?_
  have kab := ka.trans kb
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (kab.scr hs) j start bit hi hbit
    ((kab.gpr _ (by decide)).trans hc) ((kab.gpr _ (by decide)).trans hstart)
    ((kab.bit _ hi).trans hb)) fun c ⟨cm, kc⟩ => ?_
  have kce : Keep base b c := Keep.of_keeps kc (by decide)
  refine WP.mono (pointSelect_ok ((kab.trans kce).scr hs) cm) fun t ⟨kt, tv, _⟩ => ?_
  refine ⟨(kab.trans kce).trans kt, ?_⟩
  rw [tv, kc.mem, savedPoint_congr _ _ bh, av, bp, ap]
  simp only [decide_eq_true_eq]

theorem baseAccumulateBody_ok {s : State} {base : Addr} (hs : Scr s base)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hi : start + n < 512)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (n + 1)) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + n))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + n)) % 2))
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : tablePoint s.mem base (5376 + 128 * n) = cache (powerPoint p (start + n))) :
    WP isa (.block baseAccumulateBody) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 n ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧ CounterKeep base s t := by
  rw [baseAccumulateBody, WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n hc) fun a ⟨ac, ka⟩ => ?_
  refine WP.mono (baseAccumulate_ok (hs.of_keeps ka (by decide)) n start
    ((scalar / 2 ^ (start + n)) % 2) (powerPoint p (start + n)) hn hi (by omega) ac
    ((ka.gpr _ (by decide)).trans hstart) (by rw [ka.mem]; exact hb) (by rw [ka.mem]; exact ht))
    fun b ⟨kb, bp⟩ => ?_
  have bc : b.gpr .x19 = BitVec.ofNat 64 n := (kb.gpr _ (by decide)).trans ac
  refine ⟨bc, ?_, (CounterKeep.of_keeps ka (by decide)).trans (CounterKeep.of_keep kb)⟩
  rw [bp, ka.mem, hp, ← after_step]

structure BaseAccumulateInv (s₀ : State) (base : Addr) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 n
  startReg : s.gpr .x1 = BitVec.ofNat 64 start
  value : point (env s.mem base) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)
  table : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = cache (powerPoint p (start + i))
  keep : CounterKeep base s₀ s

theorem baseAccumulateLoop_ok {s₀ : State} {base : Addr} (start scalar : Nat)
    (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (h₀ : BaseAccumulateInv s₀ base start scalar p 16 s₀) :
    WP isa (.loop (.block baseAccumulateBody) (.nonzero .x .x19)) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = after scalar p start ∧ CounterKeep base s₀ t := by
  apply WP.loop (BaseAccumulateInv s₀ base start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (baseAccumulateBody_ok h.scratch k start scalar p hk (by omega) h.counter
      h.startReg (h.bits k hk) (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tv, tk⟩ => ?_
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, read_x, tc, point_counter_nonzero 0 (by decide),
        show decide ((0 : Nat) ≠ 0) = false from rfl], tv, h.keep.trans tk⟩
    · refine Or.inr ⟨by simp only [eval, read_x, tc, point_counter_nonzero k hk, decide_eq_true hk0],
        k, by omega, ⟨by omega, by omega, tk.scr h.scratch, tc,
          (tk.gpr _ (by decide) (by decide)).trans h.startReg, tv, ?_, ?_, h.keep.trans tk⟩⟩
      · intro i hi'
        rw [tk.mem _ (by rw [ofs_off' base (by omega)]; omega), h.bits i hi']
      · intro i hi'
        rw [workspace_tablePoint tk.mem (by omega) (by omega), h.table i hi']
  · exact h₀

theorem baseAccumulate16_ok {s : State} {base : Addr} (hs : Scr s base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = cache (powerPoint p (start + i))) :
    WP isa baseAccumulate16 s fun t => point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      CounterKeep base s t := by
  rw [baseAccumulate16]
  refine WP.seq (WP.mono (accumulateInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  refine WP.mono (baseAccumulateLoop_ok start scalar p hi
    ⟨by decide, by decide, hs.of_keeps ka (by decide), ac, (ka.gpr _ (by decide)).trans hstart,
      by rw [ka.mem]; exact hp, by rw [ka.mem]; exact hb, by rw [ka.mem]; exact ht,
      CounterKeep.refl _ _⟩) fun t ⟨tv, tk⟩ => ?_
  exact ⟨tv, (CounterKeep.of_keeps ka (by decide)).trans tk⟩

end VG.Proof.Ed25519.AArch64
