import VerifiedGarbage.Impl.Ed25519.X86_64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.BaseTable
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop

/-!
# Adding cached powers, sixteen scalar bits at a time

Untrusted. The cached addition is the specification's `pointAdd` (`ring`),
and the loop over a batch's sixteen bits is `accumulateLoop_ok`'s, with the
local table holding cached powers.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)
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

theorem pointAddCachedWide_ok {s : State} {base : Addr} (hs : Scratch s base)
    (q : Spec.Ed25519.Point) (hq : point (env s.mem base) 4 5 6 7 = cache q) :
    WP isa (.block pointAddCached) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCodeWide_ok hs pointAddCachedOps) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointAddCached_eval _ q hq, pointAddCached_high _⟩

theorem baseAccumulate_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j start bit : Nat) (q : Spec.Ed25519.Point) (hj : j < 16) (hi : start + j < 512) (hbit : bit < 2)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit)
    (hq : tablePoint s.mem base (5376 + 128 * j) = cache q) :
    WP isa (.block baseAccumulate) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 =
        (if bit = 0 then point (env s.mem base) 0 1 2 3 else
          Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q) ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [baseAccumulate, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (prepareAdd_ok hs j hj hc) fun a ⟨ka, ap, aq, av, ad⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointAddCachedWide_ok (hs.of_keep ka) q (aq.trans hq)) fun b ⟨kb, bp, bh⟩ => ?_
  have kab := ka.trans kb
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (hs.of_keep kab) j start bit hi hbit
    ((kab.gpr _ (by decide)).trans hc) ((kab.gpr _ (by decide)).trans hstart)
    ((kab.bit _ hi).trans hb)) fun c ⟨cm, kc⟩ => ?_
  have kce : Keep base b c := Keep.of_keeps kc (by decide)
  refine WP.mono (pointSelect_ok (hs.of_keep (kab.trans kce)) cm) fun t ⟨kt, tv, td⟩ => ?_
  refine ⟨(kab.trans kce).trans kt, ?_, ?_⟩
  · rw [tv, kc.2.1, savedPoint_congr _ _ bh, av, bp, ap]
    simp only [decide_eq_true_eq]
  · rw [td, kc.2.1, bh 16 (by decide), ad]

theorem baseAccumulateBody_ok {s : State} {base : Addr} (hs : Scratch s base)
    (n start scalar : Nat) (p : Spec.Ed25519.Point) (hn : n < 16) (hi : start + n < 512)
    (hc : s.gpr .rbx = BitVec.ofNat 64 (n + 1)) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + n))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + n)) % 2))
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + n + 1))
    (ht : tablePoint s.mem base (5376 + 128 * n) = cache (powerPoint p (start + n))) :
    WP isa (.block baseAccumulateBody) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 n ∧ t.zf = some (decide (n = 0)) ∧
      point (env t.mem base) 0 1 2 3 = after scalar p (start + n) ∧
      env t.mem base 16 = env s.mem base 16 ∧ RbxKeep base s t := by
  rw [baseAccumulateBody, List.append_assoc, WP.block_append_iff]
  refine WP.mono (accumulateDec_ok s n hc) fun a ⟨ac, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (baseAccumulate_ok (hs.of_keeps ka (by decide)) n start ((scalar / 2 ^ (start + n)) % 2)
    (powerPoint p (start + n)) hn hi (by omega) ac ((ka.1 _ (by decide)).trans hstart)
    (by rw [ka.2.1]; exact hb)
    (by rw [ka.2.1]; exact ht)) fun b ⟨kb, bp, bd⟩ => ?_
  have bc : b.gpr .rbx = BitVec.ofNat 64 n := (kb.gpr _ (by decide)).trans ac
  refine WP.mono (accumulateTest_ok b n hn bc) fun t ⟨tz, kt⟩ => ?_
  refine ⟨(kt.1 _ (by simp)).trans bc, tz, ?_, ?_, ?_⟩
  · rw [kt.2.1, bp, ka.2.1, hp, ← after_step]
  · rw [kt.2.1, bd, ka.2.1]
  · exact ((RbxKeep.of_keeps ka (by decide)).trans (RbxKeep.of_keep kb)).trans
      (RbxKeep.of_keeps kt (by decide))

structure BaseAccumulateInv (s₀ : State) (base : Addr) (start scalar : Nat)
    (p : Spec.Ed25519.Point) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scratch s base
  counter : s.gpr .rbx = BitVec.ofNat 64 n
  startReg : s.gpr .rsi = BitVec.ofNat 64 start
  d : env s.mem base 16 = env s₀.mem base 16
  value : point (env s.mem base) 0 1 2 3 = after scalar p (start + n)
  bits : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2)
  table : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = cache (powerPoint p (start + i))
  keep : RbxKeep base s₀ s

theorem baseAccumulateLoop_ok {s₀ : State} {base : Addr} (hs : Scratch s₀ base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hc : s₀.gpr .rbx = 16) (hstart : s₀.gpr .rsi = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s₀.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hp : point (env s₀.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s₀.mem base (5376 + 128 * i) = cache (powerPoint p (start + i))) :
    WP isa (.loop (.block baseAccumulateBody) .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = env s₀.mem base 16 ∧ RbxKeep base s₀ t := by
  apply WP.loop (BaseAccumulateInv s₀ base start scalar p) (n := 16)
  · intro n s h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hk : k < 16 := by have := h.bound; omega
    refine WP.mono (baseAccumulateBody_ok h.scratch k start scalar p hk (by omega) h.counter h.startReg
      (h.bits k hk) (by rw [Nat.add_assoc]; exact h.value) (h.table k hk))
      fun t ⟨tc, tz, tv, td, tk⟩ => ?_
    have hb' : ∀ i < 16, t.mem (off base (768 + (start + i))) =
        BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2) := by
      intro i hi'
      rw [tk.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits i hi']
    have ht' : ∀ i < 16, tablePoint t.mem base (5376 + 128 * i) = cache (powerPoint p (start + i)) := by
      intro i hi'
      rw [workspace_tablePoint tk.mem (by omega) (by omega), h.table i hi']
    by_cases hk0 : k = 0
    · subst hk0
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv,
        td.trans h.d, h.keep.trans tk⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hk0, Option.map_some, Bool.not_false],
        k, by omega, ⟨by omega, by omega, tk.scratch h.scratch, tc,
          (tk.gpr _ (by decide) (by decide)).trans h.startReg, td.trans h.d, tv, hb', ht',
          h.keep.trans tk⟩⟩
  · exact ⟨by decide, by decide, hs, hc, hstart, rfl, hp, hb, ht, RbxKeep.refl _ _⟩

theorem baseAccumulate16_ok {s : State} {base : Addr} (hs : Scratch s base)
    (start scalar : Nat) (p : Spec.Ed25519.Point) (hi : start + 16 ≤ 512)
    (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : ∀ i < 16, s.mem (off base (768 + (start + i))) = BitVec.ofNat 8 ((scalar / 2 ^ (start + i)) % 2))
    (hp : point (env s.mem base) 0 1 2 3 = after scalar p (start + 16))
    (ht : ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = cache (powerPoint p (start + i))) :
    WP isa baseAccumulate16 s fun t => point (env t.mem base) 0 1 2 3 = after scalar p start ∧
      env t.mem base 16 = env s.mem base 16 ∧ RbxKeep base s t := by
  rw [baseAccumulate16]
  refine WP.seq (WP.mono (accumulateInit_ok s) fun a ⟨ac, ka⟩ => ?_)
  refine WP.mono (baseAccumulateLoop_ok (hs.of_keeps ka (by decide)) start scalar p hi ac
    ((ka.1 _ (by decide)).trans hstart) (by rw [ka.2.1]; exact hb)
    (by rw [ka.2.1]; exact hp) (by rw [ka.2.1]; exact ht))
    fun t ⟨tv, td, tk⟩ => ?_
  exact ⟨tv, by rw [td, ka.2.1], (RbxKeep.of_keeps ka (by decide)).trans tk⟩

end VG.Proof.Ed25519.X86_64
