import VerifiedGarbage.Proof.Ed25519.X86_64.BaseAccumulate
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseBatchTable
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul

/-!
# Base-point multiplication from the cached table

Untrusted. As `pointMulBatch_ok` and `pointMulLoop_ok`, but each batch's
powers come from `baseCached` rather than from doubling a checkpoint.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off Keeps clob Outside)

theorem baseMulBatch_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j scalar : Nat) (hj : j < 16)
    (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1))
    (hp : point (env s.mem base) 0 1 2 3 = after scalar Spec.Ed25519.basePoint (16 * (j + 1)))
    (hb : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa baseMulBatch s fun t =>
      t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧ t.zf = some (decide (j = 0)) ∧
      point (env t.mem base) 0 1 2 3 = after scalar Spec.Ed25519.basePoint (16 * j) ∧
      (∀ i < 16 * 16, t.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) ∧
      env t.mem base 16 = env s.mem base 16 ∧ PowersKeep base 56 7368 s t := by
  rw [baseMulBatch]
  refine WP.seq (WP.mono (batchBegin_ok hs j hc) fun a ⟨ac, av, ag, ar, aw, am⟩ => ?_)
  have ka : PowersKeep base 56 7368 s a := ⟨fun r hr _ _ => ag r hr, ar, aw,
    (TableFrame.table am).mono (by decide) (by decide)⟩
  have ae := header_env am
  refine WP.seq (WP.mono (baseBatchTable_ok (ka.scratch hs) j hj ac) fun b hb' => ?_)
  have kb := hb'.powersKeep
  have bcounter : b.mem.readW (off base 56) 64 = BitVec.ofNat 64 j :=
    ((tableFrame_outside kb.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans av
  have bbits : ∀ i < 16 * 16, b.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2) := by
    intro i hi
    rw [kb.mem.bits i (by omega), am _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), hb i hi]
  have btable : ∀ i < 16, tablePoint b.mem base (5376 + 128 * i) =
      cache (powerPoint Spec.Ed25519.basePoint (16 * j + i)) := by
    intro i hi
    rw [hb'.table i hi, baseCached_ok _ (by omega)]
  have bpoint : point (env b.mem base) 0 1 2 3 = after scalar Spec.Ed25519.basePoint (16 * j + 16) := by
    rw [table_env hb'.mem (by decide), ae, hp, Nat.mul_add, Nat.mul_one]
  have kab : PowersKeep base 56 7368 s b := ka.trans (kb.mono (by decide) (by decide))
  refine WP.seq (WP.mono (batchBitOffset_ok (kab.scratch hs) j (by omega) bcounter) fun c ⟨cs, kc⟩ => ?_)
  have kce : PowersKeep base 56 7368 b c := PowersKeep.of_keeps kc (by decide)
  have kabc := kab.trans kce
  refine WP.seq (WP.mono (baseAccumulate16_ok (kabc.scratch hs) (16 * j) scalar Spec.Ed25519.basePoint (by omega) cs
    (by intro i hi; rw [kc.2.1]; exact bbits _ (by omega))
    (by rw [kc.2.1]; exact bpoint) (by rw [kc.2.1]; exact btable))
    fun d ⟨dp, dd, kd⟩ => ?_)
  have dcounter : d.mem.readW (off base 56) 64 = BitVec.ofNat 64 j :=
    (kd.mem.word (d := 56) (Or.inl (by decide)) (by decide)).trans
      ((congrArg (fun m : Mem => m.readW (off base 56) 64) kc.2.1).trans bcounter)
  have kabcd : PowersKeep base 56 7368 s d := kabc.trans (PowersKeep.of_rbx kd)
  refine WP.mono (batchTest_ok (kabcd.scratch hs) j (by omega) dcounter) fun t ⟨tz, kt⟩ => ?_
  refine ⟨?_, tz, ?_, ?_, ?_, kabcd.trans (PowersKeep.of_keeps kt (by decide))⟩
  · rw [kt.2.1]; exact dcounter
  · rw [kt.2.1]; exact dp
  · intro i hi
    rw [kt.2.1, kd.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), kc.2.1]
    exact bbits i hi
  · rw [kt.2.1, dd, kc.2.1, table_env hb'.mem (by decide), ae]

structure BaseMulInv (s₀ : State) (base : Addr) (scalar : Nat) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scratch s base
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 n
  value : point (env s.mem base) 0 1 2 3 = after scalar Spec.Ed25519.basePoint (16 * n)
  bits : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)
  slot16 : env s.mem base 16 = env s₀.mem base 16
  keep : PowersKeep base 56 7368 s₀ s

theorem baseMulLoop_ok {s₀ : State} {base : Addr} (scalar : Nat) (h₀ : BaseMulInv s₀ base scalar 16 s₀) :
    WP isa (.loop baseMulBatch .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint ∧
      PowersKeep base 56 7368 s₀ t := by
  apply WP.loop (BaseMulInv s₀ base scalar) (n := 16)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < 16 := by have := h.bound; omega
    refine WP.mono (baseMulBatch_ok h.scratch j scalar hj h.counter h.value h.bits)
      fun t ⟨tc, tz, tv, tb, td, tk⟩ => ?_
    by_cases hj0 : j = 0
    · subst hj0
      rw [Nat.mul_zero, after_zero] at tv
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv,
        h.keep.trans tk⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hj0, Option.map_some, Bool.not_false],
        j, by omega, ⟨by omega, by omega, tk.scratch h.scratch, tc, tv, tb, td.trans h.slot16,
          h.keep.trans tk⟩⟩
  · exact h₀

theorem baseMultiplyInit_ok {s : State} {base : Addr} (hs : Scratch s base)
    (scalar : Nat) (hscalar : scalar < 2 ^ (16 * 16))
    (hb : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa (.block baseMultiplyInit) s (BaseMulInv s base scalar 16) := by
  rw [baseMultiplyInit, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs (constPointOps Spec.Ed25519.identity)) fun b ⟨kb, vb⟩ => ?_
  have kbp : PowersKeep base 56 7368 s b := PowersKeep.of_keep kb
  refine WP.mono (mulCounterInit_ok (kbp.scratch hs) 16) fun c ⟨cc, cg, cr, cw, cm⟩ => ?_
  have kc : PowersKeep base 56 7368 b c := ⟨fun r _ _ hr => cg r (by
    intro he; subst r; exact hr (by decide)), cr, cw, (TableFrame.table cm).mono (by decide) (by decide)⟩
  refine ⟨by decide, Nat.le_refl _, (kbp.trans kc).scratch hs, cc, ?_, ?_, ?_, kbp.trans kc⟩
  · rw [header_env cm, vb, constPoint_eval, after_top _ _ _ hscalar]
  · intro i hi
    rw [cm _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), kb.bit _ (by omega), hb i hi]
  · rw [header_env cm, vb]; rfl

theorem baseMultiply_ok {s : State} {base : Addr} (hs : Scratch s base)
    (scalar : Nat) (hscalar : scalar < 2 ^ (16 * 16))
    (hb : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa baseMultiply s fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint ∧
      PowersKeep base 56 7368 s t := by
  rw [baseMultiply]
  refine WP.seq (WP.mono (baseMultiplyInit_ok hs scalar hscalar hb) fun a h => ?_)
  refine WP.mono (baseMulLoop_ok scalar ⟨h.positive, h.bound, h.scratch, h.counter, h.value, h.bits,
    rfl, PowersKeep.refl _ _ _ _⟩) fun t ⟨tv, kt⟩ => ?_
  exact ⟨tv, h.keep.trans kt⟩

end VG.Proof.Ed25519.X86_64
