import VerifiedGarbage.Proof.Curve448.AArch64.Fast.Butterfly

/-!
# `a + 39081 e`

Untrusted: everything here is checked by Lean. Limb `i` of the result is
`a_i + (39081 e_i mod 2⁵⁶) + c_{i-1}` (and `+ c₇` for limb 4), with
`c_i = ⌊39081 e_i / 2⁵⁶⌋` and `c_{-1} = c₇`.
-/

namespace VG.Proof.Curve448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.Curve448.AArch64.Fast
open VG.Impl.X448.AArch64 (ld st ACC)
open VG.Proof.X448.Wide (radix)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside writeW_outside limbs FieldMem ofs read8_eq
  write8_eq)
open VG.Proof.Ed25519.AArch64 (read_x)

def smallRegs : List Reg :=
  [.x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x13, .x14, .x15, .x16, .x17, .x21, .x22, .x23, .x24]

theorem small_mem : ∀ i < 8, smallX i ∈ smallRegs ∧ smallC i ∈ smallRegs := by decide
theorem small_not : ∀ i < 8, smallX i ∉ [Reg.x0, .x2, .x24, .x3, .x12] ∧
    smallC i ∉ [Reg.x0, .x2, .x24, .x3, .x12] ∧ smallX i ≠ smallC i := by decide
theorem small_inj : ∀ i < 8, ∀ j < 8, j ≠ i → smallX j ≠ smallX i ∧ smallC j ≠ smallC i ∧
    smallX j ≠ smallC i ∧ smallC j ≠ smallX i := by decide

/-- The carry of limb `i`. -/
def sc (e : Nat → Nat) (i : Nat) : Nat := 39081 * e i / radix

/-- Limb `i` before the carries. -/
def sl (a e : Nat → Nat) (i : Nat) : Nat := a i + 39081 * e i % radix

theorem smallLimb_val (x e : BitVec 64) (hx : x.toNat + 2 ^ 56 ≤ 2 ^ 64) (he : e.toNat < 2 ^ 59) :
    (x + e * BitVec.ofNat 64 39081 - (BitVec.ofNat 64 (e.toNat * 10004736 / 2 ^ 64) <<< 56)).toNat =
      x.toNat + 39081 * e.toNat % radix ∧
    (BitVec.ofNat 64 (e.toNat * 10004736 / 2 ^ 64)).toNat = 39081 * e.toNat / radix := by
  have hc : e.toNat * 10004736 / 2 ^ 64 = 39081 * e.toNat / radix := by
    simp only [radix]; omega
  rw [hc]
  have hcl : 39081 * e.toNat / radix < 2 ^ 64 := by simp only [radix]; omega
  refine ⟨?_, by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hcl⟩
  generalize hl : 39081 * e.toNat % radix = l
  generalize hcc : 39081 * e.toNat / radix = c at hcl
  have hm : l + radix * c = 39081 * e.toNat := by rw [← hl, ← hcc]; exact Nat.mod_add_div _ _
  have hlt : l < radix := by rw [← hl]; exact Nat.mod_lt _ (by decide)
  have h1 : c * 2 ^ 56 % 2 ^ 64 = c % 2 ^ 8 * 2 ^ 56 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 8 * 2 ^ 56 by decide, Nat.mul_mod_mul_right]
  have h2 : e.toNat * 39081 % 2 ^ 64 = l + c % 2 ^ 8 * 2 ^ 56 := by
    rw [Nat.mul_comm, ← hm]
    simp only [radix] at hlt ⊢
    omega
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hcl,
    show 39081 % 2 ^ 64 = 39081 by decide, h1, h2]
  simp only [radix] at hlt ⊢
  omega

def K39 : BitVec 64 := BitVec.ofNat 64 39081
def K8 : BitVec 64 := BitVec.ofNat 64 10004736

theorem smallConsts_ok (s : State) :
    WP isa (.block [.movz .x .x0 39081 0, .movz .x .x2 0xa900 0, .movk .x .x2 0x0098 1]) s fun t =>
      t.gpr .x0 = K39 ∧ t.gpr .x2 = K8 ∧ t.mem = s.mem ∧ Keeps [.x0, .x2] s t := by
  refine WP.of_runBlock ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
      show 16 * 0 < 64 from by decide, show 16 * 1 < 64 from by decide, ite_true]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false]; decide
  · simp only [State.read, RegUpd.gpr_write, ite_true]; decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2, ite_false]

theorem smallLimbStep_ok {t : State} {base : Addr} (ht : Scr t base) {a e i : Nat} (hi : i < 8)
    (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ha8 : a % 8 = 0) (he8 : e % 8 = 0)
    (h0 : t.gpr .x0 = K39) (h2 : t.gpr .x2 = K8) :
    WP isa (.block (smallLimb a e i)) t fun u =>
      u.gpr (smallX i) = word t.mem base (a + 8 * i) + word t.mem base (e + 8 * i) * K39 -
        (BitVec.ofNat 64 ((word t.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56) ∧
      u.gpr (smallC i) = BitVec.ofNat 64 ((word t.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) ∧
      u.mem = t.mem ∧ Keeps [.x24, smallX i, smallC i] t u := by
  obtain ⟨re, ae, ra, aa⟩ := ld2 ht (d := e + 8 * i) (e := a + 8 * i) (by omega) (by omega) (by omega)
    (by omega)
  obtain ⟨n1, n2, n3⟩ := small_not i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at n1 n2
  obtain ⟨x0, x2, x24, x3, -⟩ := n1
  obtain ⟨c0, c2, c24, c3, -⟩ := n2
  refine WP.of_runBlock ⟨_, by
    simp only [smallLimb, ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
      Size.bits, State.load, read_x, RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write,
      RegUpd.wr_write, x24, Ne.symm x24, reduceCtorEq, ite_true, ite_false, ht.x3, ae, aa, re, ra, and_self,
      show 56 < 64 from by decide, Option.map_some, Option.bind_some]; rfl, ?_⟩
  refine ⟨?_, ?_, rfl, fun q hq => ?_, rfl, rfl⟩
  · have k8 : (BitVec.ofNat 64 10004736 : BitVec 64).toNat = 10004736 := rfl
    simp only [RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, x24, 
      n3, Ne.symm x0, Ne.symm x2, read8_eq, h0, h2,
      K8, k8]
  · have k8 : (BitVec.ofNat 64 10004736 : BitVec 64).toNat = 10004736 := rfl
    simp only [RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, c24, 
      Ne.symm n3, n3, Ne.symm x2, read8_eq, h2, K8, k8]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hq
    simp only [RegUpd.gpr_write, hq.1, hq.2.1, hq.2.2, ite_false]

theorem smallLoop1_ok {s : State} {base : Addr} (hs : Scr s base) {a e : Nat}
    (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ha8 : a % 8 = 0) (he8 : e % 8 = 0)
    (h0 : s.gpr .x0 = K39) (h2 : s.gpr .x2 = K8) :
    WP isa (.block ((List.range 8).flatMap (smallLimb a e))) s fun t =>
      (∀ i < 8, t.gpr (smallX i) = word s.mem base (a + 8 * i) + word s.mem base (e + 8 * i) * K39 -
        (BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56)) ∧
      (∀ i < 8, t.gpr (smallC i) = BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64)) ∧
      t.mem = s.mem ∧ Keeps smallRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, t.gpr (smallX i) = word s.mem base (a + 8 * i) + word s.mem base (e + 8 * i) * K39 -
      (BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64) <<< 56)) ∧
    (∀ i < n, t.gpr (smallC i) = BitVec.ofNat 64 ((word s.mem base (e + 8 * i)).toNat * 10004736 / 2 ^ 64)) ∧
    t.mem = s.mem ∧ Keeps smallRegs s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tx, tc, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (smallLimbStep_ok ts hn ha he ha8 he8 ((tk.1 _ (by decide)).trans h0)
    ((tk.1 _ (by decide)).trans h2)) fun u ⟨ux, uc, um, uk⟩ => ?_
  have nk : ∀ i < 8, i ≠ n → smallX i ∉ [Reg.x24, smallX n, smallC n] ∧
      smallC i ∉ [Reg.x24, smallX n, smallC n] := by
    intro i hi h
    obtain ⟨q1, q2, -⟩ := small_not i hi
    obtain ⟨r1, r2, r3, r4⟩ := small_inj n hn i hi h
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at q1 q2 ⊢
    exact ⟨⟨q1.2.2.1, r1, r3⟩, ⟨q2.2.2.1, r4, r2⟩⟩
  refine ⟨fun i hi => ?_, fun i hi => ?_, um.trans tm, tk.trans (uk.mono fun r hr => ?_)⟩
  · by_cases h : i = n
    · subst h; rw [ux, tm]
    · rw [uk.1 _ (nk i (by omega) h).1, tx i (by omega)]
  · by_cases h : i = n
    · subst h; rw [uc, tm]
    · rw [uk.1 _ (nk i (by omega) h).2, tc i (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · decide
    · exact (small_mem n hn).1
    · exact (small_mem n hn).2

def smallStore (o i : Nat) : List Instr :=
  [.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++
    (if i = 4 then [.add .x (smallX i) (smallX i) (smallC 7)] else []) ++ [st (smallX i) (o + 8 * i)]

theorem small_split (o a e : Nat) :
    small o a e = ([.movz .x .x0 39081 0, .movz .x .x2 0xa900 0, .movk .x .x2 0x0098 1] : List Instr) ++
      (List.range 8).flatMap (smallLimb a e) ++ (List.range 8).flatMap (smallStore o) := rfl

/-- The value `smallStore` writes. -/
def smallOut (X C : Nat → BitVec 64) (i : Nat) : BitVec 64 :=
  X i + C ((i + 7) % 8) + if i = 4 then C 7 else 0

theorem smallCX : ∀ i < 8, smallC ((i + 7) % 8) ≠ smallX i ∧ smallC 7 ≠ smallX i := by decide

theorem smallStore_ok {t : State} {base : Addr} (ht : Scr t base) {o i : Nat} (hi : i < 8)
    (ho : o + 64 ≤ 8192) (ho8 : o % 8 = 0) :
    WP isa (.block (smallStore o i)) t fun u =>
      (∀ d, d + 8 ≤ 8192 → (d = o + 8 * i ∨ d + 8 ≤ o + 8 * i ∨ o + 8 * i + 8 ≤ d) →
        word u.mem base d = if d = o + 8 * i then smallOut (fun j => t.gpr (smallX j)) (fun j => t.gpr (smallC j)) i else word t.mem base d) ∧
      Outside base (o + 8 * i) 8 t.mem u.mem ∧ Keeps [smallX i] t u := by
  obtain ⟨cx, c7⟩ := smallCX i hi
  have hx3 := (small_not i hi).1
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx3
  by_cases h4 : i = 4
  · subst h4
    simp only [smallStore, ite_true, List.cons_append, List.nil_append]
    rw [show [Instr.add .x (smallX 4) (smallX 4) (smallC ((4 + 7) % 8)),
        .add .x (smallX 4) (smallX 4) (smallC 7), st (smallX 4) (o + 8 * 4)] =
        [Instr.add .x (smallX 4) (smallX 4) (smallC ((4 + 7) % 8))] ++
        [Instr.add .x (smallX 4) (smallX 4) (smallC 7)] ++ [st (smallX 4) (o + 8 * 4)] from rfl,
      List.append_assoc, WP.block_append_iff]
    refine WP.mono (add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
    rw [WP.block_append_iff]
    refine WP.mono (add_ok u _ _ _) fun v ⟨vv, vm, vk⟩ => ?_
    have vs : Scr v base := (ht.of_keeps uk (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)).of_keeps vk
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)
    refine WP.mono (stw_ok vs _ (d := o + 8 * 4) (by omega) (by omega))
      fun w ⟨ww, wo, wg, wr, wwr⟩ => ⟨fun d hd hs => ?_, by rw [← um, ← vm]; exact wo,
        ⟨fun q hq => ?_, wr.trans (vk.2.1.trans uk.2.1), wwr.trans (vk.2.2.trans uk.2.2)⟩⟩
    · rw [ww d hd hs, vv, vm, um, uk.1 (smallC 7) (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact c7), uv]
      by_cases e : d = o + 8 * 4
      · rw [ite_eq_left e, ite_eq_left e]; simp only [smallOut, ite_true]
      · rw [ite_eq_right e, ite_eq_right e]
    · rw [wg, vk.1 q hq, uk.1 q hq]
  · simp only [smallStore, h4, ite_false, List.append_nil]
    rw [show [Instr.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++ [st (smallX i) (o + 8 * i)] =
        [Instr.add .x (smallX i) (smallX i) (smallC ((i + 7) % 8))] ++ [st (smallX i) (o + 8 * i)] from rfl,
      WP.block_append_iff]
    refine WP.mono (add_ok t _ _ _) fun u ⟨uv, um, uk⟩ => ?_
    have us : Scr u base := ht.of_keeps uk (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact ⟨Ne.symm hx3.2.2.2.1, Ne.symm hx3.2.2.2.2⟩)
    refine WP.mono (stw_ok us _ (d := o + 8 * i) (by omega) (by omega))
      fun w ⟨ww, wo, wg, wr, wwr⟩ => ⟨fun d hd hs => ?_, by rw [← um]; exact wo,
        ⟨fun q hq => ?_, wr.trans uk.2.1, wwr.trans uk.2.2⟩⟩
    · rw [ww d hd hs, uv, um]
      by_cases e : d = o + 8 * i
      · rw [ite_eq_left e, ite_eq_left e]; simp only [smallOut, h4, ite_false]; exact (BitVec.add_zero _).symm
      · rw [ite_eq_right e, ite_eq_right e]
    · rw [wg, uk.1 q hq]

theorem smallLoop2_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 64 ≤ 8192)
    (ho8 : o % 8 = 0) :
    WP isa (.block ((List.range 8).flatMap (smallStore o))) s fun t =>
      (∀ i < 8, word t.mem base (o + 8 * i) =
        smallOut (fun j => s.gpr (smallX j)) (fun j => s.gpr (smallC j)) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps smallRegs s t := by
  let inv := fun n (t : State) =>
    (∀ i < n, word t.mem base (o + 8 * i) =
      smallOut (fun j => s.gpr (smallX j)) (fun j => s.gpr (smallC j)) i) ∧
    (∀ i < 8, n ≤ i → t.gpr (smallX i) = s.gpr (smallX i)) ∧
    (∀ i < 8, t.gpr (smallC i) = s.gpr (smallC i)) ∧
    Outside base o (8 * n) s.mem t.mem ∧ Keeps smallRegs s t
  refine WP.mono (wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tx, tc, tO, tk⟩ => ?_) 8
    (by decide) s ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl, fun _ _ => rfl,
      Outside.refl _ _ _ _, Keeps.refl _ _⟩) fun t ⟨tv, _, _, tO, tk⟩ => ⟨tv, tO, tk⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (smallStore_ok ts hn ho ho8) fun u ⟨uw, uO, uk⟩ => ⟨fun i hi => ?_, fun i hi hni => ?_,
    fun i hi => ?_, ?_, tk.trans (uk.mono fun r hr => ?_)⟩
  · rw [uw _ (by omega) (by omega)]
    by_cases h : i = n
    · subst h
      rw [ite_eq_left rfl]
      simp only [smallOut, tx i hn (Nat.le_refl _), tc _ (Nat.mod_lt _ (by decide)), tc 7 (by decide)]
    · rw [ite_eq_right (by omega)]; exact tv i (by omega)
  · have := (small_inj n hn i hi (by omega)).1
    rw [uk.1 _ (by simp [this]), tx i hi (by omega)]
  · by_cases h : i = n
    · subst h; rw [uk.1 _ (by simp [(small_not i hi).2.2.symm]), tc i hi]
    · rw [uk.1 _ (by simp [(small_inj n hn i hi h).2.2.2]), tc i hi]
  · rw [show 8 * (n + 1) = 8 * n + 8 by omega]
    intro x hx
    rw [uO x (by omega), tO x (by omega)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hr]; exact (small_mem n hn).1

/-- The limbs `small` writes, from the operands' limbs. -/
def smallVal (a e : Nat → Nat) (i : Nat) : Nat :=
  sl a e i + sc e ((i + 7) % 8) + if i = 4 then sc e 7 else 0

theorem small_ok {s : State} {base : Addr} (hs : Scr s base) {o a e : Nat}
    (ho : o + 64 ≤ 8192) (ha : a + 64 ≤ 8192) (he : e + 64 ≤ 8192) (ho8 : o % 8 = 0) (ha8 : a % 8 = 0)
    (he8 : e % 8 = 0) (fa : ∀ i < 8, limbs s.mem base a i < Mb) (fe : ∀ i < 8, limbs s.mem base e i < Ib) :
    WP isa (.block (small o a e)) s fun t =>
      (∀ i < 8, limbs t.mem base o i = smallVal (limbs s.mem base a) (limbs s.mem base e) i) ∧
      Outside base o 64 s.mem t.mem ∧ Keeps (.x0 :: .x2 :: smallRegs) s t := by
  rw [small_split, List.append_assoc, WP.block_append_iff]
  refine WP.mono (smallConsts_ok s) fun t ⟨t0, t2, tm, tk⟩ => ?_
  have ts : Scr t base := hs.of_keeps tk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (smallLoop1_ok ts ha he ha8 he8 t0 t2) fun u ⟨ux, uc, um, uk⟩ => ?_
  have us : Scr u base := ts.of_keeps uk (by decide)
  refine WP.mono (smallLoop2_ok us ho ho8) fun w ⟨wv, wo, wk⟩ => ⟨fun i hi => ?_, ?_,
    (tk.mono (by decide)).trans ((uk.mono (by decide)).trans (wk.mono (by decide)))⟩
  · have lv : ∀ j < 8, (u.gpr (smallX j)).toNat = sl (limbs s.mem base a) (limbs s.mem base e) j ∧
        (u.gpr (smallC j)).toNat = sc (limbs s.mem base e) j := by
      intro j hj
      have hb := fa j hj; have hb' := fe j hj
      simp only [Mb, Ib] at hb hb'
      have := smallLimb_val (word s.mem base (a + 8 * j)) (word s.mem base (e + 8 * j))
        (by simp only [limbs] at hb; omega) (by simp only [limbs] at hb'; omega)
      rw [ux j hj, uc j hj, tm]
      exact this
    have hc : ∀ j < 8, sc (limbs s.mem base e) j < 2 ^ 20 := by
      intro j hj; have := fe j hj; simp only [sc, Ib, radix] at this ⊢; omega
    have hsl : sl (limbs s.mem base a) (limbs s.mem base e) i < 2 ^ 58 := by
      have := fa i hi; have := Nat.mod_lt (39081 * limbs s.mem base e i) (show 0 < radix by decide)
      simp only [sl, Mb, radix] at *; omega
    change (word w.mem base (o + 8 * i)).toNat = _
    rw [wv i hi]
    simp only [smallOut, smallVal]
    have h7 := (lv 7 (by decide)).2
    have hj := (lv ((i + 7) % 8) (Nat.mod_lt _ (by decide))).2
    have hx := (lv i hi).1
    have c7 := hc 7 (by decide)
    have cj := hc ((i + 7) % 8) (Nat.mod_lt _ (by decide))
    split
    · rw [BitVec.toNat_add, BitVec.toNat_add, hx, hj, h7]
      omega
    · rw [BitVec.toNat_add, BitVec.toNat_add, hx, hj, show (0 : BitVec 64).toNat = 0 from rfl]
      omega
  · intro x hx
    rw [wo x hx, um, tm]

end VG.Proof.Curve448.AArch64.Fast
