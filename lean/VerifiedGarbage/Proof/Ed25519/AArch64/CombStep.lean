import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import Mathlib.Tactic.Ring

/-!
# The comb's additions, negation and doublings

`pointAddMixed` adds an affine cached point (`Z = 1`, so its `2Z` is `2` and
the product `Z₁ · 2Z₂` is `Z₁ + Z₁`) exactly as the specification's
`pointAdd`; `combNeg` negates the selected cached point under the sign's mask;
`double4` doubles four times, exactly.
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

/-! ## The mixed additions -/

/-- What `addOddOps` and `addEvenOps` compute, from the accumulator's coordinates and the cached
entry's. -/
def mixedResult (x y z t q₀ q₁ q₂ : Spec.X25519.Fe) : Spec.Ed25519.Point :=
  let a := (y - x) * q₀
  let b := (y + x) * q₁
  let c := t * q₂
  let dd := z + z
  ⟨(b - a) * (dd - c), (dd + c) * (b + a), (dd - c) * (dd + c), (b - a) * (b + a)⟩

theorem mixedResult_eq (p q : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (q.Y - q.X) (q.Y + q.X) (q.T * 2 * Spec.Ed25519.d) =
      Spec.Ed25519.pointAdd p q := by
  simp only [mixedResult, Spec.Ed25519.pointAdd, hz]
  congr 1 <;> ring

theorem addOdd_formula (e : Env) :
    point (evalOps addOddOps e) 0 1 2 3 = mixedResult (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6) := rfl

theorem addEven_formula (e : Env) :
    point (evalOps addEvenOps e) 17 18 19 20 =
      mixedResult (e 17) (e 18) (e 19) (e 20) (e 13) (e 14) (e 15) := rfl

theorem mixed_eval {e : Env} {a b c : Slot} {q : Spec.Ed25519.Point}
    (hq : cachedAt e a b c = cache q) (p : Spec.Ed25519.Point) (hz : q.Z = 1) :
    mixedResult p.X p.Y p.Z p.T (e a) (e b) (e c) = Spec.Ed25519.pointAdd p q := by
  have h4 : e a = q.Y - q.X := congrArg Spec.Ed25519.Point.X hq
  have h5 : e b = q.Y + q.X := congrArg Spec.Ed25519.Point.Y hq
  have h6 : e c = q.T * 2 * Spec.Ed25519.d := congrArg Spec.Ed25519.Point.Z hq
  rw [h4, h5, h6, mixedResult_eq p q hz]

theorem addOdd_ok {s : State} {base : Addr} (hs : Scr s base)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem base) 4 5 6 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addOddOps)) s fun t =>
      Keep base s t ∧ point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) q ∧
      ∀ i : Slot, (4 ≤ i.val ∧ i.val < 8 ∨ 13 ≤ i.val) → env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok addOddOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addOdd_formula _).trans (mixed_eval hq (point (env s.mem base) 0 1 2 3) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addOddOps, (fieldDest op).val < 4 ∨ (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) :=
    by decide
  have := this op hop
  rw [← h] at this
  omega

theorem addEven_ok {s : State} {base : Addr} (hs : Scr s base)
    (q : Spec.Ed25519.Point) (hq : cachedAt (env s.mem base) 13 14 15 = cache q) (hz : q.Z = 1) :
    WP isa (.block (fieldCode addEvenOps)) s fun t =>
      Keep base s t ∧ point (env t.mem base) 17 18 19 20 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 17 18 19 20) q ∧
      ∀ i : Slot, (i.val < 8 ∨ 13 ≤ i.val ∧ i.val < 17 ∨ 21 ≤ i.val) →
        env t.mem base i = env s.mem base i := by
  refine WP.mono (fieldCode_ok addEvenOps hs) fun t ⟨hk, hv⟩ => ?_
  rw [hv]
  refine ⟨hk, (addEven_formula _).trans (mixed_eval hq (point (env s.mem base) 17 18 19 20) hz),
    fun i hi => ?_⟩
  apply evalOps_unchanged
  intro op hop h
  have : ∀ op ∈ addEvenOps, (8 ≤ (fieldDest op).val ∧ (fieldDest op).val < 13) ∨
      (17 ≤ (fieldDest op).val ∧ (fieldDest op).val < 21) := by decide
  have := this op hop
  rw [← h] at this
  omega

/-! ## The negations -/

private theorem index3_fact : ∀ j < 32, BitVec.ofNat 64 j <<< 3 = BitVec.ofNat 64 (8 * j) := by
  decide +kernel

private theorem bit_mask : ∀ b < 2,
    ((BitVec.ofNat 8 b).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 = mask (decide (b = 0)) := by
  decide

theorem nib_neg (S i : Nat) : decide (nib S i < 8) = decide ((S / 2 ^ (4 * i + 3)) % 2 = 0) := by
  rw [nib_bits]
  have h0 := Nat.mod_lt (S / 2 ^ (4 * i)) (show 2 > 0 by decide)
  have h1 := Nat.mod_lt (S / 2 ^ (4 * i + 1)) (show 2 > 0 by decide)
  have h2 := Nat.mod_lt (S / 2 ^ (4 * i + 2)) (show 2 > 0 by decide)
  have h3 := Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide)
  apply decide_eq_decide.mpr
  omega

theorem signLoad_ok {s : State} {base : Addr} (hs : Scr s base) {S j i o : Nat} (hj : j < 32)
    (hi : i < 64) (hoi : 8 * j + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa (.block [.lsl .x .x3 .x19 3, .add .x .x3 .x0 .x3, .ldrb .x3 .x3 (o + 3),
      .subImm .x .x3 .x3 1]) s fun t =>
      t.gpr .x3 = mask (decide (nib S i < 8)) ∧ Keeps [.x3] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (4 * i + 3))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (o + 3) = off base (768 + (4 * i + 3)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hv := bit_mask _ (Nat.mod_lt (S / 2 ^ (4 * i + 3)) (show 2 > 0 by decide))
  rw [← hb _ (by omega), ← nib_neg] at hv
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, State.load, addr, Size.bits,
    show (3 : Nat) < 64 from by decide, show (1 : Nat) < 4096 from by decide,
    show o + 3 < 4096 * 1 by omega, Nat.mod_one, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    hc, index3_fact j hj, hs.x0, he, hr, read_byte, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- The negation, on the environment. -/
theorem neg_env (e : Env) (a b c : Slot) (sw : Bool) (hab : a ≠ b) (hc8 : c ≠ 8) (ha : a ≠ 8)
    (hb : b ≠ 8) (hac : a ≠ c) (hbc : b ≠ c) (hz : e 21 = 0) :
    cachedAt (swapEnvs [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e)) a b c =
      if sw then negCached (cachedAt e a b c) else cachedAt e a b c := by
  cases sw <;> simp [cachedAt, negCached, swapEnvs, swapEnv, evalOps, evalOp,
    hab, hc8, ha, hb, ha.symm, hb.symm, hac, hac.symm, hbc, hbc.symm, hz]

theorem neg_other (e : Env) (a b c : Slot) (sw : Bool) (i : Slot) (ha : i ≠ a) (hb : i ≠ b)
    (hc : i ≠ c) (h8 : i ≠ 8) :
    swapEnvs [(a, b), (c, 8)] sw (evalOps [.sub 8 21 c] e) i = e i := by
  cases sw <;> simp [swapEnvs, swapEnv, evalOps, evalOp, Function.update_apply, ha, hb, hc, h8]

theorem combNeg_ok {s : State} {base : Addr} (hs : Scr s base) {S j i o : Nat} (a b c : Slot)
    (hj : j < 32) (hi : i < 64) (hoi : 8 * j + o = 768 + 4 * i) (ho : o + 3 < 4096)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2))
    (hdis : ∀ ab ∈ [(a, b), (c, (8 : Slot))], ab.1 ≠ ab.2) :
    WP isa (.block (combNeg a b c o)) s fun t => Keep base s t ∧
      env t.mem base = swapEnvs [(a, b), (c, 8)] (decide (nib S i < 8))
        (evalOps [.sub 8 21 c] (env s.mem base)) := by
  rw [combNeg, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.sub 8 21 c] hs) fun u ⟨ku, vu⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (signLoad_ok (S := S) (ku.scr hs) hj hi hoi ho ((ku.gpr _ (by decide)).trans hc)
    (fun q hq => by rw [ku.mem _ (by rw [ofs_off' base (by omega)]; omega)]; exact hb q hq))
    fun v ⟨v3, kv⟩ => ?_
  have kuv : Keep base u v := Keep.of_keeps kv (by decide)
  refine WP.mono (swapFields_ok ((ku.trans kuv).scr hs) [(a, b), (c, 8)] hdis v3)
    fun t ⟨kt, _, vt⟩ => ⟨(ku.trans kuv).trans kt, ?_⟩
  rw [vt, kv.mem, vu]

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
