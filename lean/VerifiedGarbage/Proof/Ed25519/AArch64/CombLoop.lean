import VerifiedGarbage.Proof.Ed25519.AArch64.CombSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers
import Mathlib.Tactic.Ring

/-! Merged from `Proof.Ed25519.AArch64.CombStep`. -/
section
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
  have _hcap : workSize true = 8192 := rfl
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
end

/-!
# The comb's loop

After step `j`, the accumulator `A` (slots 0–3) represents `[G + Σ_{i < j}
d_{2i+1} 256^i]B` and `B` (slots 17–20) represents `[G + Σ_{i < j} d_{2i}
256^i]B` (`CombDigits`); at the end, `16 A + B` is the scalar's multiple.
-/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519 VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519 Edwards
open Word64

/-- The loop's invariant, after `j` steps. -/
structure CombInv (s₀ : State) (base : Addr) (S j : Nat) (s : State) : Prop where
  bound : j ≤ 32
  scratch : Scr s base
  counter : s.gpr .x19 = BitVec.ofNat 64 j
  zero : env s.mem base 21 = 0
  bits : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)
  odd : Rep (point (env s.mem base) 0 1 2 3) ((combGVal + oddSumZ S j) • baseAff)
  even : Rep (point (env s.mem base) 17 18 19 20) ((combGVal + evenSumZ S j) • baseAff)
  keep : CombKeep base s₀ s

private theorem next_fact : ∀ j < 32,
    BitVec.ofNat 64 j + BitVec.ofNat 64 1 = BitVec.ofNat 64 (j + 1) ∧
    (BitVec.ofNat 64 (j + 1) - BitVec.ofNat 64 32 != 0) = decide (j + 1 ≠ 32) := by decide +kernel

theorem combNext_ok (s : State) {j : Nat} (hj : j < 32) (h : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block [.addImm .x .x19 .x19 1, .subImm .x .x8 .x19 32]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (j + 1) ∧ (t.gpr .x8 != 0) = decide (j + 1 ≠ 32) ∧
      Keeps [.x19, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec_addImm_x (show 1 < 4096 by decide),
    exec_subImm_x (show 32 < 4096 by decide), read_x, RegUpd.gpr_write, BitVec.setWidth_eq, h,
    (next_fact j hj).1, (next_fact j hj).2, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem Frame2.slots {base : Addr} {m m' : Mem} (h : Frame2 base (offset 4) (offset 13) 96 m m') :
    Outside base 64 704 m m' := fun x hx => h x (by simp only [offset]; omega) (by simp only [offset]; omega)

theorem Frame2.env {base : Addr} {m m' : Mem} (h : Frame2 base (offset 4) (offset 13) 96 m m')
    (i : Slot) (hi : i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) : env m' base i = env m base i :=
  h.F (by simp only [offset]; omega) (by simp only [offset]; omega) (by simp only [offset]; omega)

private theorem dis_odd : ∀ ab ∈ [((4 : Slot), (5 : Slot)), (6, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

private theorem dis_even : ∀ ab ∈ [((13 : Slot), (14 : Slot)), (15, 8)], ab.1 ≠ ab.2 := by
  intro ab hab; simp only [List.mem_cons, List.not_mem_nil, or_false] at hab
  rcases hab with rfl | rfl <;> decide

theorem combStep_ok {s₀ s : State} {base : Addr} {S j : Nat} (h : CombInv s₀ base S j s)
    (hj : j < 32) :
    WP isa combStep s fun t => (t.gpr .x8 != 0) = decide (j + 1 ≠ 32) ∧
      CombInv s₀ base S (j + 1) t := by
  rw [combStep]
  have no := nib_lt S (2 * j + 1)
  have ne := nib_lt S (2 * j)
  -- Both digits' masks.
  refine WP.seq (WP.mono (combDigits_ok h.scratch hj h.counter h.bits) fun a ha => ?_)
  have hsa : Scr a base := h.scratch.of_keeps ha.keeps (by decide)
  have a19 : a.gpr .x19 = BitVec.ofNat 64 j := (ha.keeps.gpr _ (by decide)).trans h.counter
  have hm : Masks (mag (nib S (2 * j + 1))) (mag (nib S (2 * j))) a :=
    ⟨ha.oddMask, ha.evenMask, ha.oddZero, ha.evenZero⟩
  have ksa : CombKeep base s a := CombKeep.of_keeps ha.keeps (by
    intro r hr
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr
    · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl hr))
  -- Both entries.
  refine WP.seq (WP.mono (combSelectFrom_ok (List.range 32) (fun k hk => List.mem_range.mp hk) hsa
    (mag_lt no) (mag_lt ne) hm (List.mem_range.mpr hj) hj a19) fun b ⟨bo, be, bf, kb⟩ => ?_)
  have hsb : Scr b base := ⟨(kb.1 _ (by decide)).trans hsa.x0, kb.2.2.1 ▸ hsa.wr, hsa.nowrap⟩
  have b19 : b.gpr .x19 = BitVec.ofNat 64 j := (kb.1 _ (by decide)).trans a19
  have kab : CombKeep base a b := ⟨fun r _ _ hc => kb.1 r (fun hm => hc (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide)), kb.2.1, kb.2.2.1, kb.2.2.2, bf.slots⟩
  have ksb := ksa.trans kab
  have bbits : ∀ q < 256, b.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => by rw [ksb.bit hq]; exact h.bits q hq
  have eb : ∀ i : Slot, (i.val < 4 ∨ (7 ≤ i.val ∧ i.val < 13) ∨ 16 ≤ i.val) →
      env b.mem base i = env s.mem base i := fun i hi => by
    rw [bf.env i hi, ha.keeps.mem]
  -- The odd entry, negated for a negative digit, and added.
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (combNeg_ok hsb (S := S) (i := 2 * j + 1) 4 5 6 hj (by omega) (by omega) (by decide)
    b19 bbits dis_odd) fun c ⟨kc, vc⟩ => ?_
  obtain ⟨qo, hqo, hqoz, hrqo⟩ := combEntry_ok j (nib S (2 * j + 1)) hj no
  have b21 : env b.mem base 21 = 0 := (eb 21 (by decide)).trans h.zero
  have co : cachedAt (env c.mem base) 4 5 6 = cache qo := by
    rw [vc, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      b21, bo, ← hqo]
    by_cases hlt : nib S (2 * j + 1) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ec : ∀ i : Slot, (i.val < 4 ∨ 9 ≤ i.val) → env c.mem base i = env b.mem base i := fun i hi => by
    rw [vc, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  rw [WP.block_append_iff]
  refine WP.mono (addOdd_ok (kc.scr hsb) qo co hqoz) fun d ⟨kd, dp, dh⟩ => ?_
  -- The even entry, negated for a negative digit, and added.
  rw [WP.block_append_iff]
  have hsd : Scr d base := kd.scr (kc.scr hsb)
  have d19 : d.gpr .x19 = BitVec.ofNat 64 j := by
    rw [kd.gpr _ (by decide), kc.gpr _ (by decide)]; exact b19
  have dbits : ∀ q < 256, d.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2) :=
    fun q hq => by rw [(CombKeep.of_keep (kc.trans kd)).bit hq]; exact bbits q hq
  refine WP.mono (combNeg_ok hsd (S := S) (i := 2 * j) 13 14 15 hj (by omega) (by omega) (by decide)
    d19 dbits dis_even) fun f ⟨kf, vf⟩ => ?_
  obtain ⟨qe, hqe, hqez, hrqe⟩ := combEntry_ok j (nib S (2 * j)) hj ne
  have ed : ∀ i : Slot, 13 ≤ i.val → env d.mem base i = env b.mem base i := fun i hi => by
    rw [dh i (Or.inr hi), ec i (Or.inr (by omega))]
  have fe : cachedAt (env f.mem base) 13 14 15 = cache qe := by
    rw [vf, neg_env _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ((ed 21 (by decide)).trans b21)]
    have : cachedAt (env d.mem base) 13 14 15 = cachedAt (env b.mem base) 13 14 15 := by
      simp only [cachedAt, ed 13 (by decide), ed 14 (by decide), ed 15 (by decide)]
    rw [this, be, ← hqe]
    by_cases hlt : nib S (2 * j) < 8 <;> simp only [hlt, decide_true, decide_false, ↓reduceIte,
      Bool.false_eq_true]
  have ef : ∀ i : Slot, (i.val < 8 ∨ 16 ≤ i.val) → env f.mem base i = env d.mem base i := fun i hi => by
    rw [vf, neg_other _ _ _ _ _ i (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide) (fun e => by subst e; revert hi; decide)
      (fun e => by subst e; revert hi; decide)]
  rw [WP.block_append_iff]
  refine WP.mono (addEven_ok (kf.scr hsd) qe fe hqez) fun g ⟨kg, gp, gh⟩ => ?_
  have g19 : g.gpr .x19 = BitVec.ofNat 64 j := by
    rw [kg.gpr _ (by decide), kf.gpr _ (by decide)]; exact d19
  refine WP.mono (combNext_ok g hj g19) fun t ⟨t19, t8, kt⟩ => ⟨t8, ?_⟩
  have kbt : CombKeep base b t :=
    ((((CombKeep.of_keep kc).trans (CombKeep.of_keep kd)).trans (CombKeep.of_keep kf)).trans
      (CombKeep.of_keep kg)).trans (CombKeep.of_keeps kt (by decide))
  have kst := ksb.trans kbt
  -- Slots 0–3 after the odd addition; 17–20 after the even one.
  have eg : ∀ i : Slot, i.val < 4 → env g.mem base i = env d.mem base i := fun i hi => by
    rw [gh i (Or.inl (by omega)), ef i (Or.inl (by omega))]
  have pc : point (env c.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, ec 0 (by decide), ec 1 (by decide), ec 2 (by decide), ec 3 (by decide),
      eb 0 (by decide), eb 1 (by decide), eb 2 (by decide), eb 3 (by decide)]
  have pf : point (env f.mem base) 17 18 19 20 = point (env s.mem base) 17 18 19 20 := by
    simp only [point, ef 17 (by decide), ef 18 (by decide), ef 19 (by decide), ef 20 (by decide),
      ed 17 (by decide), ed 18 (by decide), ed 19 (by decide), ed 20 (by decide),
      eb 17 (by decide), eb 18 (by decide), eb 19 (by decide), eb 20 (by decide)]
  refine ⟨by omega, kbt.scr hsb, t19, ?_, fun q hq => ?_, ?_, ?_, h.keep.trans kst⟩
  · rw [kt.mem, gh 21 (Or.inr (Or.inr (by decide))), ef 21 (by decide), ed 21 (by decide)]
    exact b21
  · rw [kst.bit hq]; exact h.bits q hq
  · have pg : point (env g.mem base) 0 1 2 3 = point (env d.mem base) 0 1 2 3 := by
      simp only [point, eg 0 (by decide), eg 1 (by decide), eg 2 (by decide), eg 3 (by decide)]
    rw [kt.mem, pg, dp, pc, oddSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.odd hrqo
  · rw [kt.mem, gp, pf, evenSumZ, ← add_assoc, add_smul]
    exact pointAdd_rep h.even hrqe

/-! ## The loop and the end -/

theorem combInit_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block combInit) s fun t => CombKeep base s t ∧ env t.mem base 21 = 0 ∧
      point (env t.mem base) 0 1 2 3 = combG ∧ point (env t.mem base) 17 18 19 20 = combG ∧
      t.gpr .x19 = BitVec.ofNat 64 0 := by
  rw [combInit, WP.block_append_iff]
  refine WP.mono (fieldCode_ok _ hs) fun a ⟨ka, va⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨(CombKeep.of_keep ka).trans ⟨fun r hr _ _ => RegUpd.gpr_write_of_ne _ _ _ hr,
    rfl, rfl, rfl, Outside.refl _ _ _ _⟩, ?_, ?_, ?_, ?_⟩
  · simp only [RegUpd.mem_write, va]; rfl
  · simp only [RegUpd.mem_write, va]; rfl
  · simp only [RegUpd.mem_write, va]; rfl
  · rw [RegUpd.gpr_write_self]; rfl

theorem combFinish_ok {s : State} {base : Addr} (hs : Scr s base) {v w : ℤ}
    (ha : Rep (point (env s.mem base) 0 1 2 3) (v • baseAff))
    (hb : Rep (point (env s.mem base) 17 18 19 20) (w • baseAff)) :
    WP isa combFinish s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) ((16 * v + w) • baseAff) ∧ CombKeep base s t := by
  rw [combFinish]
  refine WP.seq (WP.mono (fieldCode_ok [.const 16 Spec.Ed25519.d] hs) fun a ⟨ka, va⟩ => ?_)
  have hsa := ka.scr hs
  have ea : ∀ i : Slot, i ≠ 16 → env a.mem base i = env s.mem base i := fun i hi => by
    rw [va]; exact evalOps_unchanged _ _ i (by simpa [fieldDest] using hi)
  have ad : env a.mem base 16 = Spec.Ed25519.d := by rw [va]; rfl
  refine WP.seq (WP.mono (double4_ok hsa ad) fun b ⟨bp, bh, kb⟩ => ?_)
  have hsb := kb.scratch hsa
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] hsb)
    fun c ⟨kc, vc⟩ => ?_
  have hsc := kc.scr hsb
  have cd : env c.mem base 16 = Spec.Ed25519.d := by
    rw [vc, show evalOps [.copy 4 17, .copy 5 18, .copy 6 19, .copy 7 20] (env b.mem base) 16 =
      env b.mem base 16 from rfl, bh 16 (by decide), ad]
  refine WP.mono (pointAdd_ok hsc cd) fun t ⟨kt, tp, _⟩ => ?_
  refine ⟨?_, (((CombKeep.of_keep ka).trans (CombKeep.of_double kb)).trans (CombKeep.of_keep kc)).trans
    (CombKeep.of_keep kt)⟩
  have p0 : point (env c.mem base) 0 1 2 3 = point (env b.mem base) 0 1 2 3 := by rw [vc]; rfl
  have p4 : point (env c.mem base) 4 5 6 7 = point (env s.mem base) 17 18 19 20 := by
    rw [vc]
    show point (env b.mem base) 17 18 19 20 = _
    simp only [point, bh 17 (by decide), bh 18 (by decide), bh 19 (by decide), bh 20 (by decide),
      ea 17 (by decide), ea 18 (by decide), ea 19 (by decide), ea 20 (by decide)]
  have pa : point (env a.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 := by
    simp only [point, ea 0 (by decide), ea 1 (by decide), ea 2 (by decide), ea 3 (by decide)]
  rw [tp, p0, p4, bp, pa, ← zsmul_16]
  have h4 := powerPoint_rep ha 4
  rw [show (2 ^ 4 : Nat) = 16 from rfl] at h4
  exact pointAdd_rep h4 hb

theorem combMultiply_ok {s : State} {base : Addr} (hs : Scr s base) {S : Nat} (hS : S < 2 ^ 256)
    (hb : ∀ q < 256, s.mem (off base (768 + q)) = BitVec.ofNat 8 ((S / 2 ^ q) % 2)) :
    WP isa combMultiply s fun t =>
      Rep (point (env t.mem base) 0 1 2 3) (S • baseAff) ∧ CombKeep base s t := by
  rw [combMultiply]
  refine WP.seq (WP.mono (combInit_ok hs) fun b ⟨kb, bz, bp, bq, b19⟩ => ?_)
  have hg : Rep combG (((combGVal : ℤ) + 0) • baseAff) := by
    rw [add_zero, natCast_zsmul]; exact combG_ok
  have init : CombInv s base S 0 b :=
    ⟨by decide, kb.scr hs, b19, bz, fun q hq => by rw [kb.bit hq]; exact hb q hq,
      by rw [bp]; exact hg, by rw [bq]; exact hg, kb⟩
  have hl : WP isa (.loop combStep (.nonzero .x .x8)) b fun t => CombInv s base S 32 t := by
    apply WP.loop (fun n t => CombInv s base S (32 - n) t ∧ 0 < n ∧ n ≤ 32) (n := 32)
    · intro n t ⟨ht, hn0, hn⟩
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      refine WP.mono (combStep_ok ht (by omega)) fun u ⟨u8, hu⟩ => ?_
      by_cases hk : k = 0
      · subst hk
        exact Or.inl ⟨by simp only [eval, read_x, u8, show 32 - (0 + 1) + 1 = 32 from rfl, ne_eq,
          not_true_eq_false, decide_false], hu⟩
      · refine Or.inr ⟨by simp only [eval, read_x, u8, show 32 - (k + 1) + 1 ≠ 32 by omega, ne_eq,
          not_false_eq_true, decide_true], k, by omega, ?_, by omega, by omega⟩
        rw [show 32 - k = 32 - (k + 1) + 1 by omega]; exact hu
    · exact ⟨init, by decide, by decide⟩
  refine WP.seq (WP.mono hl fun t ht => ?_)
  refine WP.mono (combFinish_ok ht.scratch ht.odd ht.even) fun u ⟨hu, ku⟩ => ⟨?_, ht.keep.trans ku⟩
  rw [comb_total hS, natCast_zsmul] at hu
  exact hu

end VG.Proof.Ed25519.AArch64
