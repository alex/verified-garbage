import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulVarCT
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseMultiply
import VerifiedGarbage.Proof.Ed25519.X86_64.PointFromScalar

/-!
# Variable-time scalar multiplication: batches and complete multiplications

Untrusted. As `pointMulBatch_ok`/`pointMulLoop_ok` and `baseMulBatch_ok`/
`baseMulLoop_ok`, with the variable-time bit loop.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

/-- The facts a batch keeps, with the accumulator at `after scalar p v`. -/
structure VarStage (s₀ : State) (base : Addr) (count scalar : Nat) (p : Spec.Ed25519.Point)
    (j v : Nat) (s : State) : Prop where
  scratch : Scratch s base
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar p v
  bits : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)
  table : ∀ i < count, tablePoint s.mem base (1280 + 128 * i) = powerPoint p (16 * i)
  keep : PowersKeep base 56 7368 s₀ s

theorem VarStage.of_powers {s₀ s t : State} {base : Addr} {count scalar : Nat} {p : Spec.Ed25519.Point}
    {j v : Nat} (h : VarStage s₀ base count scalar p j v s) (hn : count ≤ 32) (k : PowersKeep base 5376 2048 s t)
    (hd : env t.mem base 16 = Spec.Ed25519.d)
    (hv : point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3) :
    VarStage s₀ base count scalar p j v t := by
  refine ⟨k.scratch h.scratch, ?_, hd, hv.trans h.value, ?_, ?_,
    h.keep.trans (k.mono (by decide) (by decide))⟩
  · exact ((tableFrame_outside k.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans h.counter
  · intro i hi
    rw [k.mem.bits i (by omega), h.bits i hi]
  · intro i hi
    rw [k.mem.point (by omega) (Or.inl (by omega)) (by omega), h.table i hi]

theorem varBegin_ok {s₀ s : State} {base : Addr} {count scalar : Nat} {p : Spec.Ed25519.Point} {j : Nat}
    (hn : count ≤ 32) (h : PointMulInv s₀ base count scalar p (j + 1) s) :
    WP isa (.block batchBegin) s fun t => VarStage s₀ base count scalar p j (16 * j + 16) t ∧
      t.gpr .rbx = BitVec.ofNat 64 j := by
  refine WP.mono (batchBegin_ok h.scratch j h.counter) fun a ⟨ac, av, ag, ar, aw, am⟩ => ?_
  have ka : PowersKeep base 56 7368 s a := ⟨fun r hr _ _ => ag r hr, ar, aw,
    (TableFrame.table am).mono (by decide) (by decide)⟩
  have ae := header_env am
  refine ⟨⟨ka.scratch h.scratch, av, by rw [ae]; exact h.d, ?_, ?_, ?_, h.keep.trans ka⟩, ac⟩
  · rw [ae, h.value, Nat.mul_add, Nat.mul_one]
  · intro i hi
    rw [am _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits i hi]
  · intro i hi
    have := h.bound
    rw [(TableFrame.table am).point (by omega) (Or.inr (by omega)) (by omega), h.table i hi]

/-- After a batch's powers are in the local table. -/
def VarReady (s₀ : State) (base : Addr) (count scalar : Nat) (p : Spec.Ed25519.Point) (j : Nat)
    (s : State) : Prop :=
  VarStage s₀ base count scalar p j (16 * j + 16) s ∧
    ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) = powerPoint p (16 * j + i)

theorem varPrepare_ok {s₀ s : State} {base : Addr} {count scalar : Nat} {p : Spec.Ed25519.Point} {j : Nat}
    (hj : j < count) (hn : count ≤ 32)
    (h : VarStage s₀ base count scalar p j (16 * j + 16) s ∧ s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa prepareBatch s (VarReady s₀ base count scalar p j) := by
  refine WP.mono (prepareBatch_ok h.1.scratch j (by omega) h.2 h.1.d) fun b ⟨kb, bp, bt, bd⟩ => ?_
  refine ⟨h.1.of_powers hn kb bd bp, fun i hi => ?_⟩
  rw [bt i hi, h.1.table j hj, powerPoint_add]

theorem varOffset_ok {s₀ s : State} {base : Addr} {count scalar : Nat} {p : Spec.Ed25519.Point} {j : Nat}
    (hj : j < count) (hn : count ≤ 32) (h : VarReady s₀ base count scalar p j s) :
    WP isa (.block batchBitOffset) s fun t => VarReady s₀ base count scalar p j t ∧
      AccumulateVarPre id base (16 * j) scalar p t := by
  refine WP.mono (batchBitOffset_ok h.1.scratch j (by omega) h.1.counter) fun c ⟨cs, kc⟩ => ?_
  have kce : PowersKeep base 56 7368 s c := PowersKeep.of_keeps kc (by decide)
  have hc : VarReady s₀ base count scalar p j c := by
    refine ⟨⟨kce.scratch h.1.scratch, by rw [kc.2.1]; exact h.1.counter, by rw [kc.2.1]; exact h.1.d,
      by rw [kc.2.1]; exact h.1.value, by rw [kc.2.1]; exact h.1.bits, by rw [kc.2.1]; exact h.1.table,
      h.1.keep.trans kce⟩, by rw [kc.2.1]; exact h.2⟩
  refine ⟨hc, hc.1.scratch, cs, fun i hi => hc.1.bits _ (by omega), hc.1.d, ?_, hc.2⟩
  rw [hc.1.value]

theorem varAccumulate_ok {s₀ s : State} {base : Addr} {count scalar : Nat} {p : Spec.Ed25519.Point} {j : Nat}
    (hj : j < count) (hn : count ≤ 32)
    (h : VarReady s₀ base count scalar p j s ∧ AccumulateVarPre id base (16 * j) scalar p s) :
    WP isa (accumulateVar16 pointAdd) s (VarStage s₀ base count scalar p j (16 * j)) := by
  obtain ⟨hr, _, hstart, hb, hd, hp, ht⟩ := h
  refine WP.mono (accumulateVar16_ok (f := id) pointAdd_spec hr.1.scratch (16 * j) scalar p (by omega)
    hstart hb hd hp ht) fun d ⟨dp, dd, kd⟩ => ?_
  refine ⟨kd.scratch hr.1.scratch, ?_, dd, dp, ?_, ?_, hr.1.keep.trans (PowersKeep.of_rbx kd)⟩
  · exact (kd.mem.word (d := 56) (Or.inl (by decide)) (by decide)).trans hr.1.counter
  · intro i hi
    rw [kd.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), hr.1.bits i hi]
  · intro i hi
    rw [workspace_tablePoint kd.mem (by omega) (by omega), hr.1.table i hi]

theorem varTest_ok {s₀ s : State} {base : Addr} {count scalar : Nat} {p : Spec.Ed25519.Point} {j : Nat}
    (hj : j < count) (hn : count ≤ 32) (h : VarStage s₀ base count scalar p j (16 * j) s) :
    WP isa (.block batchTest) s fun t => VarStage s₀ base count scalar p j (16 * j) t ∧
      t.zf = some (decide (j = 0)) := by
  refine WP.mono (batchTest_ok h.scratch j (by omega) h.counter) fun t ⟨tz, kt⟩ => ?_
  refine ⟨⟨h.scratch.of_keeps kt (by decide), by rw [kt.2.1]; exact h.counter, by rw [kt.2.1]; exact h.d,
    by rw [kt.2.1]; exact h.value, by rw [kt.2.1]; exact h.bits, by rw [kt.2.1]; exact h.table,
    h.keep.trans (PowersKeep.of_keeps kt (by decide))⟩, tz⟩

theorem pointMulBatchVar_ok {s₀ s : State} {base : Addr} {count scalar : Nat} {p : Spec.Ed25519.Point}
    {j : Nat} (hj : j < count) (hn : count ≤ 32) (h : PointMulInv s₀ base count scalar p (j + 1) s) :
    WP isa pointMulBatchVar s fun t => VarStage s₀ base count scalar p j (16 * j) t ∧
      t.zf = some (decide (j = 0)) := by
  rw [pointMulBatchVar]
  refine WP.seq (WP.mono (varBegin_ok hn h) fun a ha => ?_)
  refine WP.seq (WP.mono (varPrepare_ok hj hn ha) fun b hb => ?_)
  refine WP.seq (WP.mono (varOffset_ok hj hn hb) fun c hc => ?_)
  refine WP.seq (WP.mono (varAccumulate_ok hj hn hc) fun d hd => ?_)
  exact varTest_ok hj hn hd

theorem pointMulLoopVar_ok {s₀ : State} {base : Addr} (hs : Scratch s₀ base)
    (count scalar : Nat) (p : Spec.Ed25519.Point) (hn0 : 0 < count) (hn : count ≤ 32)
    (hc : s₀.mem.readW (off base 56) 64 = BitVec.ofNat 64 count)
    (hd : env s₀.mem base 16 = Spec.Ed25519.d)
    (hp : point (env s₀.mem base) 0 1 2 3 = after scalar p (16 * count))
    (hb : ∀ i < 16 * count, s₀.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2))
    (ht : ∀ i < count, tablePoint s₀.mem base (1280 + 128 * i) = powerPoint p (16 * i)) :
    WP isa (.loop pointMulBatchVar .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar p ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ PowersKeep base 56 7368 s₀ t := by
  apply WP.loop (PointMulInv s₀ base count scalar p) (n := count)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < count := by have := h.bound; omega
    refine WP.mono (pointMulBatchVar_ok hj hn h) fun t ⟨ht, tz⟩ => ?_
    by_cases hj0 : j = 0
    · subst hj0
      have tv := ht.value
      rw [Nat.mul_zero, after_zero] at tv
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv, ht.d, ht.keep⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hj0, Option.map_some, Bool.not_false],
        j, by omega, ⟨by omega, by omega, ht.scratch, ht.counter, ht.d, ht.value, ht.bits, ht.table, ht.keep⟩⟩
  · exact ⟨hn0, Nat.le_refl _, hs, hc, hd, hp, hb, ht, PowersKeep.refl _ _ _ _⟩

theorem pointMultiplyVar_ok {s : State} {base : Addr} (hs : Scratch s base)
    (count scalar : Nat) (hn0 : 0 < count) (hn : count ≤ 32) (hscalar : scalar < 2 ^ (16 * count))
    (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * count, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa (pointMultiplyVar count) s fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar (point (env s.mem base) 0 1 2 3) ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ PowersKeep base 56 7368 s t := by
  rw [pointMultiplyVar]
  refine WP.seq (WP.mono (pointMultiplyInit_ok hs count scalar hn0 hn hscalar hd hb) fun a h => ?_)
  refine WP.mono (pointMulLoopVar_ok h.scratch count scalar _ hn0 hn h.counter h.d h.value h.bits h.table)
    fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨tv, td, h.keep.trans kt⟩

theorem pointFromScalarVar_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 32)
    (hr : ∀ q < 2 * count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 2 * count, 8192 ≤ ofs base (off k q)) :
    WP isa (pointFromScalarVar count) s fun t => PowersKeep base 56 7368 s t ∧
      point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k (2 * count)))
          (point (env s.mem base) 0 1 2 3) ∧ env t.mem base 16 = Spec.Ed25519.d := by
  rw [pointFromScalarVar]
  refine WP.seq (WP.mono (pointFromScalarPrepare_ok hs hp count hn0 hn hr hd)
    fun a ⟨ka, ap, ad, ab, av⟩ => ?_)
  refine WP.mono (pointMultiplyVar_ok (ka.scratch hs) count _ hn0 hn ab ad av) fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨ka.trans kt, (by rw [tv, ap]), td⟩

structure BaseMulVarInv (s₀ : State) (base : Addr) (scalar : Nat) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 16
  scratch : Scratch s base
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 n
  value : point (env s.mem base) 0 1 2 3 = after scalar Spec.Ed25519.basePoint (16 * n)
  bits : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)
  d : env s.mem base 16 = Spec.Ed25519.d
  keep : PowersKeep base 56 7368 s₀ s

/-- The facts a base-point batch keeps, with the accumulator at `after scalar B v`. -/
structure BaseVarStage (s₀ : State) (base : Addr) (scalar : Nat) (j v : Nat) (s : State) : Prop where
  scratch : Scratch s base
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j
  d : env s.mem base 16 = Spec.Ed25519.d
  value : point (env s.mem base) 0 1 2 3 = after scalar Spec.Ed25519.basePoint v
  bits : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)
  keep : PowersKeep base 56 7368 s₀ s

theorem baseVarBegin_ok {s₀ s : State} {base : Addr} {scalar j : Nat}
    (h : BaseMulVarInv s₀ base scalar (j + 1) s) :
    WP isa (.block batchBegin) s fun t => BaseVarStage s₀ base scalar j (16 * j + 16) t ∧
      t.gpr .rbx = BitVec.ofNat 64 j := by
  refine WP.mono (batchBegin_ok h.scratch j h.counter) fun a ⟨ac, av, ag, ar, aw, am⟩ => ?_
  have ka : PowersKeep base 56 7368 s a := ⟨fun r hr _ _ => ag r hr, ar, aw,
    (TableFrame.table am).mono (by decide) (by decide)⟩
  have ae := header_env am
  refine ⟨⟨ka.scratch h.scratch, av, by rw [ae]; exact h.d, ?_, ?_, h.keep.trans ka⟩, ac⟩
  · rw [ae, h.value, Nat.mul_add, Nat.mul_one]
  · intro i hi
    rw [am _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), h.bits i hi]

/-- After a base-point batch's cached powers are in the local table. -/
def BaseVarReady (s₀ : State) (base : Addr) (scalar j : Nat) (s : State) : Prop :=
  BaseVarStage s₀ base scalar j (16 * j + 16) s ∧
    ∀ i < 16, tablePoint s.mem base (5376 + 128 * i) =
      cache (powerPoint Spec.Ed25519.basePoint (16 * j + i))

theorem baseVarTable_ok {s₀ s : State} {base : Addr} {scalar j : Nat} (hj : j < 16)
    (h : BaseVarStage s₀ base scalar j (16 * j + 16) s ∧ s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa baseBatchTable s (BaseVarReady s₀ base scalar j) := by
  refine WP.mono (baseBatchTable_ok h.1.scratch j hj h.2) fun b hb' => ?_
  have kb := hb'.powersKeep
  have be : env b.mem base = env s.mem base := table_env hb'.mem (by decide)
  refine ⟨⟨kb.scratch h.1.scratch, ?_, by rw [be]; exact h.1.d, by rw [be]; exact h.1.value, ?_,
    h.1.keep.trans (kb.mono (by decide) (by decide))⟩, fun i hi => ?_⟩
  · exact ((tableFrame_outside kb.mem (by decide) (by decide)).word
      (d := 56) (Or.inl (by decide)) (by decide)).trans h.1.counter
  · intro i hi
    rw [kb.mem.bits i (by omega), h.1.bits i hi]
  · rw [hb'.table i hi, baseCached_ok _ (by omega)]

theorem baseVarOffset_ok {s₀ s : State} {base : Addr} {scalar j : Nat} (hj : j < 16)
    (h : BaseVarReady s₀ base scalar j s) :
    WP isa (.block batchBitOffset) s fun t => BaseVarReady s₀ base scalar j t ∧
      AccumulateVarPre cache base (16 * j) scalar Spec.Ed25519.basePoint t := by
  refine WP.mono (batchBitOffset_ok h.1.scratch j (by omega) h.1.counter) fun c ⟨cs, kc⟩ => ?_
  have kce : PowersKeep base 56 7368 s c := PowersKeep.of_keeps kc (by decide)
  have hc : BaseVarReady s₀ base scalar j c := by
    refine ⟨⟨kce.scratch h.1.scratch, by rw [kc.2.1]; exact h.1.counter, by rw [kc.2.1]; exact h.1.d,
      by rw [kc.2.1]; exact h.1.value, by rw [kc.2.1]; exact h.1.bits, h.1.keep.trans kce⟩,
      by rw [kc.2.1]; exact h.2⟩
  refine ⟨hc, hc.1.scratch, cs, fun i hi => hc.1.bits _ (by omega), hc.1.d, ?_, hc.2⟩
  rw [hc.1.value]

theorem baseVarAccumulate_ok {s₀ s : State} {base : Addr} {scalar j : Nat} (hj : j < 16)
    (h : BaseVarReady s₀ base scalar j s ∧
      AccumulateVarPre cache base (16 * j) scalar Spec.Ed25519.basePoint s) :
    WP isa (accumulateVar16 pointAddCached) s (BaseVarStage s₀ base scalar j (16 * j)) := by
  obtain ⟨hr, _, hstart, hb, hd, hp, ht⟩ := h
  refine WP.mono (accumulateVar16_ok pointAddCached_spec hr.1.scratch (16 * j) scalar _ (by omega)
    hstart hb hd hp ht) fun d ⟨dp, dd, kd⟩ => ?_
  refine ⟨kd.scratch hr.1.scratch, ?_, dd, dp, ?_, hr.1.keep.trans (PowersKeep.of_rbx kd)⟩
  · exact (kd.mem.word (d := 56) (Or.inl (by decide)) (by decide)).trans hr.1.counter
  · intro i hi
    rw [kd.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega), hr.1.bits i hi]

theorem baseVarTest_ok {s₀ s : State} {base : Addr} {scalar j : Nat} (hj : j < 16)
    (h : BaseVarStage s₀ base scalar j (16 * j) s) :
    WP isa (.block batchTest) s fun t => BaseVarStage s₀ base scalar j (16 * j) t ∧
      t.zf = some (decide (j = 0)) := by
  refine WP.mono (batchTest_ok h.scratch j (by omega) h.counter) fun t ⟨tz, kt⟩ => ?_
  refine ⟨⟨h.scratch.of_keeps kt (by decide), by rw [kt.2.1]; exact h.counter, by rw [kt.2.1]; exact h.d,
    by rw [kt.2.1]; exact h.value, by rw [kt.2.1]; exact h.bits,
    h.keep.trans (PowersKeep.of_keeps kt (by decide))⟩, tz⟩

theorem baseMulBatchVar_ok {s₀ s : State} {base : Addr} {scalar j : Nat} (hj : j < 16)
    (h : BaseMulVarInv s₀ base scalar (j + 1) s) :
    WP isa baseMulBatchVar s fun t => BaseVarStage s₀ base scalar j (16 * j) t ∧
      t.zf = some (decide (j = 0)) := by
  rw [baseMulBatchVar]
  refine WP.seq (WP.mono (baseVarBegin_ok h) fun a ha => ?_)
  refine WP.seq (WP.mono (baseVarTable_ok hj ha) fun b hb => ?_)
  refine WP.seq (WP.mono (baseVarOffset_ok hj hb) fun c hc => ?_)
  refine WP.seq (WP.mono (baseVarAccumulate_ok hj hc) fun d hd => ?_)
  exact baseVarTest_ok hj hd

theorem baseMulLoopVar_ok {s₀ : State} {base : Addr} (scalar : Nat)
    (h₀ : BaseMulVarInv s₀ base scalar 16 s₀) :
    WP isa (.loop baseMulBatchVar .ne) s₀ fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ PowersKeep base 56 7368 s₀ t := by
  apply WP.loop (BaseMulVarInv s₀ base scalar) (n := 16)
  · intro n s h
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := h.positive; omega : n ≠ 0)
    have hj : j < 16 := by have := h.bound; omega
    refine WP.mono (baseMulBatchVar_ok hj h) fun t ⟨ht, tz⟩ => ?_
    by_cases hj0 : j = 0
    · subst hj0
      have tv := ht.value
      rw [Nat.mul_zero, after_zero] at tv
      exact Or.inl ⟨by simp only [eval, tz, decide_true, Option.map_some, Bool.not_true], tv, ht.d,
        ht.keep⟩
    · exact Or.inr ⟨by simp only [eval, tz, decide_eq_false hj0, Option.map_some, Bool.not_false],
        j, by omega, ⟨by omega, by omega, ht.scratch, ht.counter, ht.value, ht.bits, ht.d, ht.keep⟩⟩
  · exact h₀

theorem baseMultiplyVar_ok {s : State} {base : Addr} (hs : Scratch s base)
    (scalar : Nat) (hscalar : scalar < 2 ^ (16 * 16)) (hd : env s.mem base 16 = Spec.Ed25519.d)
    (hb : ∀ i < 16 * 16, s.mem (off base (768 + i)) = BitVec.ofNat 8 ((scalar / 2 ^ i) % 2)) :
    WP isa baseMultiplyVar s fun t =>
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointMul scalar Spec.Ed25519.basePoint ∧
      env t.mem base 16 = Spec.Ed25519.d ∧ PowersKeep base 56 7368 s t := by
  rw [baseMultiplyVar]
  refine WP.seq (WP.mono (baseMultiplyInit_ok hs scalar hscalar hb) fun a h => ?_)
  refine WP.mono (baseMulLoopVar_ok scalar ⟨h.positive, h.bound, h.scratch, h.counter, h.value, h.bits,
    h.slot16.trans hd, PowersKeep.refl _ _ _ _⟩) fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨tv, td, h.keep.trans kt⟩

theorem baseFromScalarVar_ok {s : State} {base k : Addr} (hs : Scratch s base) (hp : s.gpr .rsi = k)
    (hr : ∀ q < 32, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < 32, 8192 ≤ ofs base (off k q)) :
    WP isa baseFromScalarVar s fun t => PowersKeep base 56 7368 s t ∧
      point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointMul (Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k 32))
          Spec.Ed25519.basePoint ∧ env t.mem base 16 = Spec.Ed25519.d := by
  rw [baseFromScalarVar]
  refine WP.seq (WP.mono (pointFromScalarPrepare_ok hs hp 16 (by decide) (by decide) hr hd)
    fun a ⟨ka, _, ad, ab, av⟩ => ?_)
  refine WP.mono (baseMultiplyVar_ok (ka.scratch hs) _ ab ad av) fun t ⟨tv, td, kt⟩ => ?_
  exact ⟨ka.trans kt, tv, td⟩

end VG.Proof.Ed25519.X86_64
