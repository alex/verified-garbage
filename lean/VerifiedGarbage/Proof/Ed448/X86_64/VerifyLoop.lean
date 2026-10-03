import VerifiedGarbage.Proof.Ed448.X86_64.VerifyField
import VerifiedGarbage.Proof.Ed448.X86_64.BaseLoop
import Mathlib.Tactic.Abel

/-!
# Ed448 verification's equation on x86-64: `[S]B + [k](-A)`

One iteration of `vloop` (`vstep_ok`), for the bits `t` of `S` (at `BITS`)
and of `k` (at `KBITS`): `Q` doubled, then `B` (slots 8–10) added and
swapped in by the first bit, and `-A` (slots 6, 7 and 10) by the second. The
loop's invariant (`VInv`): `Q` represents `[S >> n]B + [k >> n](-A)`.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448 VG.Proof.Ed448.Edwards
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask cswapE opSwap clob Outside)
open VG.Impl.X448.X86_64 (BITS slot cswap)

theorem ea_bitsAt {s : State} {base : Addr} (hr : s.gpr .rdi = base) {t : Nat}
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) (o : Nat) :
    s.ea { base := .rdi, index := some .rbx, disp := (o : Int) } = off base (o + t) := by
  simp only [State.ea, hr, hb, off, BitVec.ofInt_natCast]
  rw [BitVec.mul_one, BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm t o]

theorem maskAt_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat} (ho : o + t < 8192)
    (hb : s.gpr .rbx = BitVec.ofNat 64 t) {b : Nat} (hb2 : b < 2)
    (hbit : s.mem (off base (o + t)) = BitVec.ofNat 8 b) :
    WP isa (.block (maskAt o)) s fun s' =>
      s'.gpr .rcx = mask (decide (b = 1)) ∧ (∀ r, r ∉ [Reg.rdx, .rcx] → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hin : InRegions (s.rd ++ s.wr) (off base (o + t)) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, contains_sc (by omega)⟩
  apply WP.of_runBlock
  simp only [maskAt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    State.load8, ea_bitsAt hs.rdi hb, hin, hbit, ite_true, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, ite_false,
    reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨mask_bit b hb2, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [hr.1, hr.2, ite_false]

/-- The slots after a swap of `T` into `Q`. -/
def swapEnv (sw : Bool) (e : Env) : Env := opSwap 2 5 sw (opSwap 1 4 sw (opSwap 0 3 sw e))

/-- The slots after an iteration, for the bits `sw₁` (of `S`) and `sw₂` (of `k`). -/
def vstepEnv (sw₁ sw₂ : Bool) (e : Env) : Env :=
  swapEnv sw₂ (evalOps (addAt 6 7) (swapEnv sw₁ (evalOps (addAt 8 9) (evalOps (doubleAt 0 1 2) e))))

theorem pt_swap (sw : Bool) (e : Env) :
    pt (swapEnv sw e) 0 1 2 = if sw then pt e 3 4 5 else pt e 0 1 2 := by
  cases sw <;> rfl

theorem swapEnv_keep (sw : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val) : swapEnv sw e i = e i := by
  have h0 : i ≠ 0 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h1 : i ≠ 1 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h2 : i ≠ 2 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h3 : i ≠ 3 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h4 : i ≠ 4 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  have h5 : i ≠ 5 := fun h => by rw [h] at hi; exact absurd hi (by decide)
  simp only [swapEnv, opSwap, Function.update_of_ne h0, Function.update_of_ne h1, Function.update_of_ne h2,
    Function.update_of_ne h3, Function.update_of_ne h4, Function.update_of_ne h5]

theorem pt_congr {e e' : Env} {a b c : Index} (ha : e' a = e a) (hb : e' b = e b) (hc : e' c = e c) :
    pt e' a b c = pt e a b c := by
  simp only [pt, ha, hb, hc]

theorem vstepEnv_keep (sw₁ sw₂ : Bool) (e : Env) (i : Index) (hi : 6 ≤ i.val ∧ i.val < 12) :
    vstepEnv sw₁ sw₂ e i = e i := by
  rw [vstepEnv, swapEnv_keep _ _ _ hi.1, addAt_keep _ _ _ _ (Or.inr (Or.inl hi)), swapEnv_keep _ _ _ hi.1,
    addAt_keep _ _ _ _ (Or.inr (Or.inl hi)), doubleAt_keep0 _ _ (Or.inl ⟨by omega, hi.2⟩)]

theorem vstepEnv_pt (sw₁ sw₂ : Bool) (e : Env) :
    pt (vstepEnv sw₁ sw₂ e) 0 1 2 =
      let r₁ := Proof.Ed448.double (pt e 0 1 2)
      let r₂ := if sw₁ then addWith (e 11) r₁ (pt e 8 9 10) else r₁
      if sw₂ then addWith (e 11) r₂ (pt e 6 7 10) else r₂ := by
  -- the stages
  unfold vstepEnv
  generalize he0 : evalOps (doubleAt 0 1 2) e = e0
  have p0 : pt e0 0 1 2 = Proof.Ed448.double (pt e 0 1 2) := by rw [← he0, doubleAt_eval0]
  have k0 : ∀ i : Index, 3 ≤ i.val ∧ i.val < 12 → e0 i = e i := fun i hi => by
    rw [← he0, doubleAt_keep0 _ _ (Or.inl hi)]
  generalize he1 : evalOps (addAt 8 9) e0 = e1
  have p1 : pt e1 3 4 5 = addWith (e0 11) (pt e0 0 1 2) (pt e0 8 9 10) := by rw [← he1, addAt_eval8]
  have q1 : pt e1 0 1 2 = pt e0 0 1 2 :=
    pt_congr (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))]) (by rw [← he1, addAt_keep _ _ _ _ (Or.inl (by decide))])
  have k1 : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → e1 i = e0 i := fun i hi => by
    rw [← he1, addAt_keep _ _ _ _ (Or.inr (Or.inl hi))]
  generalize he2 : swapEnv sw₁ e1 = e2
  have p2 : pt e2 0 1 2 = if sw₁ then pt e1 3 4 5 else pt e1 0 1 2 := by rw [← he2, pt_swap]
  have k2 : ∀ i : Index, 6 ≤ i.val → e2 i = e1 i := fun i hi => by rw [← he2, swapEnv_keep _ _ _ hi]
  generalize he3 : evalOps (addAt 6 7) e2 = e3
  have p3 : pt e3 3 4 5 = addWith (e2 11) (pt e2 0 1 2) (pt e2 6 7 10) := by rw [← he3, addAt_eval6]
  have q3 : pt e3 0 1 2 = pt e2 0 1 2 :=
    pt_congr (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))])
      (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))]) (by rw [← he3, addAt_keep _ _ _ _ (Or.inl (by decide))])
  have e11 : e2 11 = e 11 := by rw [k2 11 (by decide), k1 11 (by decide), k0 11 (by decide)]
  have e11' : e0 11 = e 11 := k0 11 (by decide)
  have b8 : pt e0 8 9 10 = pt e 8 9 10 :=
    pt_congr (k0 8 (by decide)) (k0 9 (by decide)) (k0 10 (by decide))
  have a6 : pt e2 6 7 10 = pt e 6 7 10 :=
    pt_congr (by rw [k2 6 (by decide), k1 6 (by decide), k0 6 (by decide)])
      (by rw [k2 7 (by decide), k1 7 (by decide), k0 7 (by decide)])
      (by rw [k2 10 (by decide), k1 10 (by decide), k0 10 (by decide)])
  rw [pt_swap, p3, q3, p2, p1, q1, e11, e11', b8, a6, p0]

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

theorem vstep_eq : vstep fld = ([.alu .sub .rbx (.imm 1)] : List Instr) ++ (fieldCode fld (doubleAt 0 1 2) ++
    (fieldCode fld (addAt 8 9) ++ (maskAt BITS ++ (cswap (slot 0) (slot 3) ++ (cswap (slot 1) (slot 4) ++
    (cswap (slot 2) (slot 5) ++ (fieldCode fld (addAt 6 7) ++ (maskAt KBITS ++ (cswap (slot 0) (slot 3) ++
    (cswap (slot 1) (slot 4) ++ (cswap (slot 2) (slot 5) ++
    ([.alu .test .rbx (.reg .rbx)] : List Instr)))))))))))) := by
  simp only [vstep, swapT, List.append_assoc]

/-- `T` swapped into `Q` by the mask `rcx`. -/
theorem swapT_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Bool} (hc : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap (slot 0) (slot 3) ++ (cswap (slot 1) (slot 4) ++ cswap (slot 2) (slot 5)))) s
      fun s' => Keep base s s' ∧ E s'.mem base = swapEnv sw (E s.mem base) := by
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs 0 3 (by decide) hc) fun s5 ⟨k5, c5, e5⟩ => ?_
  have hs5 := k5.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (cswapE hs5 1 4 (by decide) (c5.trans hc)) fun s6 ⟨k6, c6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  refine WP.mono (cswapE hs6 2 5 (by decide) (c6.trans (c5.trans hc))) fun s7 ⟨k7, _, e7⟩ => ?_
  exact ⟨(k5.trans k6).trans k7, by rw [e7, e6, e5]; rfl⟩

include hf in
/-- An iteration, for the bits `t` of `S` (`b₁`) and of `k` (`b₂`). -/
theorem vstep_ok {s : State} {base : Addr} (hs : Scr s base) {t : Nat} (ht : t < 456)
    (hb : s.gpr .rbx = BitVec.ofNat 64 (t + 1)) {b₁ b₂ : Nat} (hb₁ : b₁ < 2) (hb₂ : b₂ < 2)
    (hbit₁ : s.mem (off base (BITS + t)) = BitVec.ofNat 8 b₁)
    (hbit₂ : s.mem (off base (KBITS + t)) = BitVec.ofNat 8 b₂) :
    WP isa (.block (vstep fld)) s fun s' =>
      s'.gpr .rbx = BitVec.ofNat 64 t ∧ s'.zf = some (decide (t = 0)) ∧
      (∀ r, r ∉ .rbx :: clob → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 64 1584 s.mem s'.mem ∧
      E s'.mem base = vstepEnv (decide (b₁ = 1)) (decide (b₂ = 1)) (E s.mem base) := by
  rw [vstep_eq, WP.block_append_iff]
  refine WP.mono (dec_ok s hb) fun s1 ⟨b1, g1, m1, rd1, wr1⟩ => ?_
  have hs1 : Scr s1 base := ⟨(g1 _ (by decide)).trans hs.rdi, wr1 ▸ hs.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf _ doubleAt_valid0 hs1) fun s2 ⟨k2, e2⟩ => ?_
  have hs2 := k2.scr hs1
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf _ addAt_valid8 hs2) fun s3 ⟨k3, e3⟩ => ?_
  have hs3 := k3.scr hs2
  have b3 : s3.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k3.gpr _ (by decide), k2.gpr _ (by decide)]; exact b1
  have hout : ∀ o, 2048 ≤ o → o + t < 8192 → Proof.X448.X86_64.ofs base (off base (o + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (o + t)) := fun o h1 h2 =>
    Or.inr (by rw [Proof.X448.X86_64.ofs_off' base (by omega)]; omega)
  have hbit3 : s3.mem (off base (BITS + t)) = BitVec.ofNat 8 b₁ := by
    rw [k3.mem _ (hout BITS (by decide) (by simp only [BITS]; omega)),
      k2.mem _ (hout BITS (by decide) (by simp only [BITS]; omega)), m1, hbit₁]
  rw [WP.block_append_iff]
  refine WP.mono (maskAt_ok hs3 (by simp only [BITS]; omega) b3 hb₁ hbit3) fun s4 ⟨c4, g4, m4, rd4, wr4⟩ => ?_
  have hs4 : Scr s4 base := ⟨(g4 _ (by decide)).trans hs3.rdi, wr4 ▸ hs3.wr, hs3.nowrap⟩
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff, List.append_assoc]
  refine WP.mono (swapT_ok hs4 c4) fun s5 ⟨k5, e5⟩ => ?_
  have hs5 := k5.scr hs4
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok hf _ addAt_valid6 hs5) fun s6 ⟨k6, e6⟩ => ?_
  have hs6 := k6.scr hs5
  have b6 : s6.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k6.gpr _ (by decide), k5.gpr _ (by decide), g4 _ (by decide)]; exact b3
  have hbit6 : s6.mem (off base (KBITS + t)) = BitVec.ofNat 8 b₂ := by
    rw [k6.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)),
      k5.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)), m4,
      k3.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)),
      k2.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega)), m1, hbit₂]
  rw [WP.block_append_iff]
  refine WP.mono (maskAt_ok hs6 (by simp only [KBITS]; omega) b6 hb₂ hbit6) fun s7 ⟨c7, g7, m7, rd7, wr7⟩ => ?_
  have hs7 : Scr s7 base := ⟨(g7 _ (by decide)).trans hs6.rdi, wr7 ▸ hs6.wr, hs6.nowrap⟩
  rw [← List.append_assoc, ← List.append_assoc, WP.block_append_iff, List.append_assoc]
  refine WP.mono (swapT_ok hs7 c7) fun s8 ⟨k8, e8⟩ => ?_
  have b8 : s8.gpr .rbx = BitVec.ofNat 64 t := by
    rw [k8.gpr _ (by decide), g7 _ (by decide)]; exact b6
  refine WP.mono (testRbx_ok s8 t ht b8) fun s' ⟨z', g', m', rd', wr'⟩ => ?_
  refine ⟨(g' _).trans b8, z', fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, not_or] at hr
    have hdc : r ∉ [Reg.rdx, .rcx] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun h => hr.2 (h ▸ by decide), fun h => hr.2 (h ▸ by decide)⟩
    rw [g', k8.gpr r hr.2, g7 r hdc, k6.gpr r hr.2, k5.gpr r hr.2, g4 r hdc, k3.gpr r hr.2, k2.gpr r hr.2,
      g1 r hr.1]
  · rw [rd', k8.rd, rd7, k6.rd, k5.rd, rd4, k3.rd, k2.rd, rd1]
  · rw [wr', k8.wr, wr7, k6.wr, k5.wr, wr4, k3.wr, k2.wr, wr1]
  · rw [m', ← m1]
    exact ((((k2.mem.trans k3.mem).trans (by rw [m4]; exact Outside.refl _ _ _ _)).trans
      (k5.mem.trans k6.mem)).trans (by rw [m7]; exact Outside.refl _ _ _ _)).trans k8.mem
  · rw [m', e8, m7, e6, e5, m4, e3, e2, m1]
    rfl

/-- One bit of both scalars: `Q` for `[S >> (t+1)]B + [k >> (t+1)]a` becomes `Q` for
`[S >> t]B + [k >> t]a`. -/
theorem rep_vstep {e : Env} {S K t : Nat} {a : EPoint dZ}
    (hr : Rep (pt e 0 1 2) ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a))
    (hq : pt e 8 9 10 = Spec.Ed448.basePoint) (ha : Rep (pt e 6 7 10) a) (hd : e 11 = Spec.Ed448.d) :
    Rep (pt (vstepEnv (decide ((S >>> t) &&& 1 = 1)) (decide ((K >>> t) &&& 1 = 1)) e) 0 1 2)
      ((S >>> t) • baseAff + (K >>> t) • a) := by
  rw [vstepEnv_pt, hd, hq]
  simp only [addWith_d]
  have h2 := double_rep hr
  have hS : (S >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hK : (K >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have e1 : (S >>> t) • baseAff + (K >>> t) • a =
      ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a) + ((S >>> (t + 1)) • baseAff + (K >>> (t + 1)) • a) +
        ((S >>> t) &&& 1) • baseAff + ((K >>> t) &&& 1) • a := by
    conv => lhs; rw [shift_step S t, shift_step K t]
    rw [add_nsmul, add_nsmul, two_mul, two_mul, add_nsmul, add_nsmul]
    abel
  rw [e1]
  generalize (S >>> t) &&& 1 = bs at *
  generalize (K >>> t) &&& 1 = bk at *
  rcases (by omega : bs = 0 ∨ bs = 1) with rfl | rfl <;> rcases (by omega : bk = 0 ∨ bk = 1) with rfl | rfl
  · simp only [zero_nsmul, add_zero, show decide ((0 : Nat) = 1) = false from rfl]; exact h2
  · simp only [zero_nsmul, add_zero, one_nsmul, show decide ((0 : Nat) = 1) = false from rfl,
      Bool.false_eq_true, ite_false]
    exact pointAdd_rep h2 ha
  · simp only [zero_nsmul, add_zero, one_nsmul, show decide ((0 : Nat) = 1) = false from rfl,
      Bool.false_eq_true, ite_false]
    exact pointAdd_rep h2 basePoint_rep
  · simp only [one_nsmul]
    exact pointAdd_rep (pointAdd_rep h2 basePoint_rep) ha

/-- The loop's invariant, after the bits above `n` of `S` and `k`, with `-A` the point `A`
(`Q`'s value only if `A` is a point of the curve: if decoding failed it is not). -/
structure VInv (base : Addr) (S K : Nat) (A : Spec.Ed448.Point) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  na : pt (E s.mem base) 6 7 10 = A
  d : E s.mem base 11 = Spec.Ed448.d
  rep : Valid A → Rep (pt (E s.mem base) 0 1 2) ((S >>> n) • baseAff + (K >>> n) • toAffine A)

include hf in
theorem vloop_ok {s₀ : State} {base : Addr} {S K : Nat} {A : Spec.Ed448.Point}
    (hbs : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1))
    (hbk : ∀ t < 456, s₀.mem (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 456 → VInv base S K A s₀ n s →
      WP isa (.loop (.block (vstep fld)) .ne) s fun s' => VInv base S K A s₀ 0 s' := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun s' => VInv base S K A s₀ 0 s')
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ VInv base S K A s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hb1 : (S >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hb2 : (K >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hout : ∀ o, 2048 ≤ o → o + t < 8192 → Proof.X448.X86_64.ofs base (off base (o + t)) < 64 ∨
      64 + 1584 ≤ Proof.X448.X86_64.ofs base (off base (o + t)) := fun o h1 h2 =>
    Or.inr (by rw [Proof.X448.X86_64.ofs_off' base (by omega)]; omega)
  have hbit1 : s.mem (off base (BITS + t)) = BitVec.ofNat 8 ((S >>> t) &&& 1) := by
    rw [hi.mem _ (hout BITS (by decide) (by simp only [BITS]; omega))]
    exact hbs t (by omega)
  have hbit2 : s.mem (off base (KBITS + t)) = BitVec.ofNat 8 ((K >>> t) &&& 1) := by
    rw [hi.mem _ (hout KBITS (by decide) (by simp only [KBITS]; omega))]
    exact hbk t (by omega)
  refine WP.mono (vstep_ok hf hi.scr (by omega) hi.rbx hb1 hb2 hbit1 hbit2)
    fun s' ⟨b', z', g', rd', wr', o', e'⟩ => ?_
  have k' : ∀ i : Index, 6 ≤ i.val ∧ i.val < 12 → E s'.mem base i = E s.mem base i := fun i hi => by
    rw [e', vstepEnv_keep _ _ _ _ hi]
  have inv : VInv base S K A s₀ t s' := by
    refine ⟨⟨(g' _ (by decide)).trans hi.scr.rdi, wr' ▸ hi.scr.wr, hi.scr.nowrap⟩, b',
      fun r hr => (g' r hr).trans (hi.gpr r hr), rd'.trans hi.rd, wr'.trans hi.wr,
      hi.mem.trans o', ?_, ?_, ?_, ?_⟩
    · rw [pt_congr (k' 8 (by decide)) (k' 9 (by decide)) (k' 10 (by decide))]; exact hi.q
    · rw [pt_congr (k' 6 (by decide)) (k' 7 (by decide)) (k' 10 (by decide))]; exact hi.na
    · rw [k' 11 (by decide)]; exact hi.d
    · intro hA; rw [e']; exact rep_vstep (hi.rep hA) hi.q (by rw [hi.na]; exact rep_toAffine hA) hi.d
  simp only [eval, z', Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false], t, by omega,
      h, by omega, inv⟩

end VG.Proof.Ed448.X86_64
