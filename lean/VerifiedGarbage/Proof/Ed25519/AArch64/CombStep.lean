import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import Mathlib.Tactic.Ring

/-!
# The comb's additions, negation and doublings

Untrusted. `pointAddMixed` adds an affine cached point (`Z = 1`, so its `2Z`
is `2` and the product `Z₁ · 2Z₂` is `Z₁ + Z₁`) exactly as the
specification's `pointAdd`; `combNeg` negates the selected cached point
under the sign's mask; `double4` doubles four times, exactly.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519
open Word64 Fin.CommRing

/-! ## Frames -/

/-- Only the registers the comb uses (`x1`, `x19` and the field operations') and the field
slots change. -/
structure CombKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x19 → r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem CombKeep.refl (base : Addr) (s : State) : CombKeep base s s :=
  ⟨fun _ _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem CombKeep.trans {base : Addr} {s t u : State} (h : CombKeep base s t)
    (k : CombKeep base t u) : CombKeep base s u :=
  ⟨fun r a b c => (k.gpr r a b c).trans (h.gpr r a b c), k.rd.trans h.rd, k.wr.trans h.wr,
    k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem CombKeep.scr {base : Addr} {s t : State} (h : CombKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem CombKeep.of_keep {base : Addr} {s t : State} (h : Keep base s t) : CombKeep base s t :=
  ⟨fun r _ _ hc => h.gpr r hc, h.rd, h.wr, h.sp, h.mem⟩

theorem CombKeep.of_double {base : Addr} {s t : State} (h : DoubleKeep base s t) : CombKeep base s t :=
  ⟨fun r _ h1 hc => h.gpr r h1 hc, h.rd, h.wr, h.sp, h.mem⟩

theorem CombKeep.of_keeps {base : Addr} {s t : State} {rs : List Reg} (h : Keeps rs s t)
    (hrs : ∀ r ∈ rs, r = .x19 ∨ r = .x1 ∨ r ∈ clob) : CombKeep base s t := by
  refine ⟨fun r h19 h1 hc => h.gpr r (fun hm => ?_), h.rd, h.wr, h.sp, by rw [h.mem]; exact Outside.refl _ _ _ _⟩
  rcases hrs r hm with h | h | h
  · exact h19 h
  · exact h1 h
  · exact hc h

theorem CombKeep.bit {base : Addr} {s t : State} (h : CombKeep base s t) {q : Nat} (hq : q < 256) :
    t.mem (off base (768 + q)) = s.mem (off base (768 + q)) :=
  h.mem _ (by rw [ofs_off' base (by omega)]; omega)

theorem CombKeep.powers {base : Addr} {s t : State} (h : CombKeep base s t) :
    PowersKeep base 56 7368 s t :=
  ⟨fun r a b c => h.gpr r a b c, h.rd, h.wr, h.sp, TableFrame.workspace h.mem⟩

/-! ## The mixed addition -/

def addMixedResult (e : Env) : Spec.Ed25519.Point :=
  let a := (e 1 - e 0) * e 4
  let b := (e 1 + e 0) * e 5
  let c := e 3 * e 6
  let dd := e 2 + e 2
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem pointAddMixed_formula (e : Env) :
    point (evalOps pointAddMixedOps e) 0 1 2 3 = addMixedResult e := rfl

theorem pointAddMixed_eval (e : Env) (q : Spec.Ed25519.Point) (hq : cachedIn e = cache q)
    (hz : q.Z = 1) :
    point (evalOps pointAddMixedOps e) 0 1 2 3 = Spec.Ed25519.pointAdd (point e 0 1 2 3) q := by
  have h4 : e 4 = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e 5 = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e 6 = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  rw [pointAddMixed_formula]
  simp only [addMixedResult, point, Spec.Ed25519.pointAdd, h4, h5, h6, hz]
  congr 1 <;> ring

theorem pointAddMixed_ok {s : State} {base : Addr} (hs : Scr s base)
    (q : Spec.Ed25519.Point) (hq : cachedIn (env s.mem base) = cache q) (hz : q.Z = 1) :
    WP isa (.block pointAddMixed) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok pointAddMixedOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  exact ⟨hk, pointAddMixed_eval _ q hq hz, point_ops_high _ (by decide) _⟩

/-! ## `[G]B` -/

def addGOps : List FieldOp :=
  [.const 4 combGCached.X, .const 5 combGCached.Y, .const 6 combGCached.Z]

theorem combAddG_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block combAddG) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) combG ∧
      ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [combAddG, WP.block_append_iff]
  refine WP.mono (fieldCode_ok addGOps hs) fun a ⟨ka, va⟩ => ?_
  have ha16 : ∀ i : Slot, 16 ≤ i.val → env a.mem base i = env s.mem base i := fun i hi => by
    rw [va]; exact point_ops_high _ (by decide) _ i hi
  have hp : point (env a.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by rw [va]; rfl
  have hc : cachedIn (env a.mem base) = cache combG := by
    rw [va, ← combGCached_eq]; rfl
  refine WP.mono (pointAddMixed_ok (ka.scr hs) combG hc rfl) fun t ⟨kt, tp, th⟩ =>
    ⟨ka.trans kt, by rw [tp, hp], fun i hi => (th i hi).trans (ha16 i hi)⟩

/-! ## The negation -/

theorem movMask_ok (s : State) :
    WP isa (.block [mov .x3 .x1]) s fun t => t.gpr .x3 = s.gpr .x1 ∧ Keeps [.x3] s t := by
  apply WP.of_runBlock
  simp only [mov, runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 0 < 4096 by decide),
    read_x, RegUpd.gpr_write_self, BitVec.setWidth_eq, BitVec.add_zero,
    Option.some.injEq, exists_eq_left']
  exact ⟨True.intro, ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa using hr), rfl, rfl, rfl, rfl⟩⟩

theorem combNeg_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool}
    (hm : s.gpr .x1 = mask sw) (hz : env s.mem base 21 = 0) :
    WP isa (.block combNeg) s fun t => Keep base s t ∧
      cachedIn (env t.mem base) =
        (if sw then negCached (cachedIn (env s.mem base)) else cachedIn (env s.mem base)) ∧
      ∀ i : Slot, (i.val < 4 ∨ 9 ≤ i.val) → env t.mem base i = env s.mem base i := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 8 21 6] hs) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movMask_ok a) fun b ⟨b3, kb⟩ => ?_
  have kab : Keep base a b := Keep.of_keeps kb (by decide)
  refine WP.mono (swapFields_ok (sw := sw) ((ka.trans kab).scr hs) [(4, 5), (6, 8)]
    (by intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
        rcases hab with rfl | rfl <;> decide)
    (b3.trans ((ka.gpr .x1 (by decide)).trans hm))) fun t ⟨kt, _, vt⟩ => ?_
  refine ⟨(ka.trans kab).trans kt, ?_, fun i hi => ?_⟩
  · rw [vt, kb.mem, va]
    cases sw <;>
      simp [cachedIn, negCached, swapEnvs, swapEnv, evalOps, evalOp, hz]
  · rw [vt, kb.mem, va]
    have h4 : i ≠ 4 := fun h => by subst h; simp at hi
    have h5 : i ≠ 5 := fun h => by subst h; simp at hi
    have h6 : i ≠ 6 := fun h => by subst h; simp at hi
    have h8 : i ≠ 8 := fun h => by subst h; simp at hi
    cases sw <;> simp [swapEnvs, swapEnv, evalOps, evalOp, h4, h5, h6, h8]

/-! ## Four doublings -/

structure Double4Inv (s₀ : State) (base : Addr) (n : Nat) (s : State) : Prop where
  positive : 0 < n
  bound : n ≤ 4
  scratch : Scr s base
  counter : s.gpr .x1 = BitVec.ofNat 64 n
  value : point (env s.mem base) 0 1 2 3 = powerPoint (point (env s₀.mem base) 0 1 2 3) (4 - n)
  high : ∀ i : Slot, 16 ≤ i.val → env s.mem base i = env s₀.mem base i
  keep : DoubleKeep base s₀ s

theorem double4_ok {s : State} {base : Addr} (hs : Scr s base)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa double4 s fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env s.mem base) 0 1 2 3) 4 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [double4]
  refine WP.seq (WP.mono (show WP isa (.block [.movz .w .x1 4 0]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 4 ∧ Keeps [.x1] s t by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
      show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    · rw [RegUpd.gpr_write_self]; rfl
    · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)) fun a ⟨ac, ka⟩ => ?_)
  have hsa : Scr a base := hs.of_keeps ka (by decide)
  have kda : DoubleKeep base s a := ⟨fun r hr _ => ka.gpr r (by simpa using hr), ka.rd, ka.wr, ka.sp,
    by rw [ka.mem]; exact Outside.refl _ _ _ _⟩
  have hl : WP isa (.loop (.block doubleBody) (.nonzero .x .x1)) a fun t =>
      point (env t.mem base) 0 1 2 3 = powerPoint (point (env a.mem base) 0 1 2 3) 4 ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env a.mem base i) ∧ DoubleKeep base a t := by
    apply WP.loop (Double4Inv a base) (n := 4)
    · intro n u hi
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hi.positive; omega : n ≠ 0)
      have hk : k < 4 := by have := hi.bound; omega
      refine WP.mono (doubleBody_ok hi.scratch k hi.counter
        ((hi.high 16 (by decide)).trans (by rw [ka.mem]; exact hd))) fun t ⟨htc, htv, hthi, htk⟩ => ?_
      have hv : point (env t.mem base) 0 1 2 3 = powerPoint (point (env a.mem base) 0 1 2 3) (4 - k) := by
        rw [htv, hi.value, show 4 - k = (4 - (k + 1)) + 1 by omega, powerPoint]
      have hh : ∀ i : Slot, 16 ≤ i.val → env t.mem base i = env a.mem base i :=
        fun i h => (hthi i h).trans (hi.high i h)
      have hkeep := hi.keep.trans htk
      by_cases hk0 : k = 0
      · subst hk0
        exact Or.inl ⟨by simp only [eval, read_x, htc, point_counter_nonzero 0 (by decide),
          show decide ((0 : Nat) ≠ 0) = false from rfl], hv, hh, hkeep⟩
      · exact Or.inr ⟨by simp only [eval, read_x, htc, point_counter_nonzero k (by omega),
          decide_eq_true hk0], k, by omega, ⟨by omega, by omega, htk.scratch hi.scratch, htc, hv, hh, hkeep⟩⟩
    · exact ⟨by decide, le_refl _, hsa, ac, rfl, fun _ _ => rfl, DoubleKeep.refl _ _⟩
  refine WP.mono hl fun t ⟨tv, th, tk⟩ => ?_
  have ea : env a.mem base = env s.mem base := by rw [ka.mem]
  rw [ea] at tv th
  exact ⟨tv, th, kda.trans tk⟩

end VG.Proof.Ed25519.AArch64
