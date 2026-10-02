import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintPack

/-!
# ML-DSA on AArch64: `vg_mldsa_hint_bit_unpack`, one polynomial

The code follows the fold form of `HintBitUnpack` (`hintBitUnpack_eq`,
`Pack/Hint.lean`) step by step: while no check has failed, the words of `h`
are the hint of the spec (`HArr`) and `x5` its index; once one has, `x5` is
256, which fails every later check (`SRel`). This file: the zeroing of `h`,
and a polynomial (`upoly_ok`): its bound, checked against the index and `ω`,
and its coefficients, each checked against the previous one plus one, which
`x11` holds (0 before the first: `prevV`).
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_lsr wp_lsl wp_ldrb wp_strw wp_addImm wp_subImm wp_movz
  wp_mov wp_orr wp_nil eval_nonzero ne_zero_iff toNat_byte toNat_ofNat_lt toNat_imm toNat_lsl_n ptr_add
  ptr_zero count_loop)
open VG.Proof.MlKem (bytesAt_getD bytesAt_length)
open VG.Proof.MlDsa.Pack

/-- `vg_mldsa_hint_bit_unpack(y = x0, len = x1, omega = w2, h = x3, hlen = x4) -> w0`. -/
def hintBitUnpackK : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, (s.gpr .x1).toNat⟩] ∧ s.wr = [⟨s.gpr .x3, (s.gpr .x4).toNat * 4⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, (s.gpr .x1).toNat⟩ ⟨s.gpr .x3, (s.gpr .x4).toNat * 4⟩ ∧
    (wArg s .x2, (s.gpr .x1).toNat - wArg s .x2) ∈ hintParams ∧ wArg s .x2 ≤ (s.gpr .x1).toNat ∧
    (s.gpr .x4).toNat = 256 * ((s.gpr .x1).toNat - wArg s .x2)
  post s s' :=
    match hintBitUnpack (wArg s .x2) ((s.gpr .x1).toNat - wArg s .x2) (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat) with
    | some hint => (s'.gpr .x0).setWidth 32 = 1 ∧ HintIs s'.mem (s.gpr .x3) ((s.gpr .x1).toNat - wArg s .x2) hint
    | none => (s'.gpr .x0).setWidth 32 = 0
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧
    s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    leakBytes (bytesAt s₁.mem (s₁.gpr .x0) (s₁.gpr .x1).toNat) =
      leakBytes (bytesAt s₂.mem (s₂.gpr .x0) (s₂.gpr .x1).toNat)

/-- The sign bit of `x - y`, tested by `cbnz`: `x < y`. -/
theorem nz_lt {x y : BitVec 64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    ((x - y) >>> 63 != 0) = decide (x.toNat < y.toNat) := by
  rw [ne_zero_iff, sub_lsr63 hx hy]
  by_cases h : x.toNat < y.toNat <;> simp [h]

/-- The sign bits of `x - y` and `z - w`, or'ed: `x < y` or `z < w`. -/
theorem nz_or {x y z w : BitVec 64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) (hz : z.toNat < 2 ^ 63)
    (hw : w.toNat < 2 ^ 63) :
    ((x - y ||| z - w) >>> 63 != 0) = decide (x.toNat < y.toNat ∨ z.toNat < w.toNat) := by
  rw [BitVec.ushiftRight_or_distrib, ne_zero_iff, BitVec.toNat_or, sub_lsr63 hx hy, sub_lsr63 hz hw]
  by_cases h₁ : x.toNat < y.toNat <;> by_cases h₂ : z.toNat < w.toNat <;> simp [h₁, h₂]

theorem toNat_ofNat_small {a : Nat} (h : a < 2 ^ 63) : (BitVec.ofNat 64 a).toNat = a :=
  toNat_ofNat_lt (by omega)

section
variable {s₀ : State} (hp : hintBitUnpackK.pre s₀)

/-- The arguments. -/
abbrev uω (s₀ : State) : Nat := wArg s₀ .x2
abbrev uk (s₀ : State) : Nat := (s₀.gpr .x1).toNat - wArg s₀ .x2
abbrev uLen (s₀ : State) : Nat := (s₀.gpr .x1).toNat
abbrev uY (s₀ : State) : Array Byte := (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat).toArray
/-- The region of `h`. -/
abbrev uR (s₀ : State) : Region := ⟨s₀.gpr .x3, (s₀.gpr .x4).toNat * 4⟩

include hp in
theorem up_facts : 4 ≤ uk s₀ ∧ uk s₀ ≤ 8 ∧ uω s₀ ≤ 80 ∧ uω s₀ + uk s₀ = uLen s₀ ∧
    (s₀.gpr .x4).toNat = 256 * uk s₀ := by
  have := mem_hintParams hp.2.2.2.1
  have := hp.2.2.2.2.1
  have := hp.2.2.2.2.2
  simp only [uk, uω, uLen] at *
  omega

/-! ## Zeroing `h` -/

/-- What `hbuInit` leaves. -/
def hbuInitPost (s₀ s : State) : Prop :=
  (∀ t < (s₀.gpr .x4).toNat, coeffAt s.mem (s₀.gpr .x3) t = 0) ∧ Frame [uR s₀] s₀.mem s.mem ∧
    s.gpr .x9 = s₀.gpr .x0 ∧ s.gpr .x3 = s₀.gpr .x3 ∧ s.gpr .x2 = s₀.gpr .x1 - (s₀.gpr .x4 >>> 8) ∧
    s.gpr .x12 = s₀.gpr .x4 >>> 8 ∧ s.rd = s₀.rd ∧ s.wr = s₀.wr ∧ s.sp = s₀.sp

include hp in
theorem hbuInit_ok : WP isa hbuInit s₀ (hbuInitPost s₀) := by
  obtain ⟨hk4, hk8, -, hsum, hr4⟩ := up_facts hp
  have hwr := hp.2.1
  have hl := (s₀.gpr .x4).isLt
  unfold hbuInit hbuPro
  refine WP.seq (wp_lsr (by decide) fun s₁ o₁ e₁ => wp_sub fun s₂ o₂ e₂ => wp_movz fun s₃ o₃ e₃ =>
    wp_mov fun s₄ o₄ e₄ => wp_mov fun s₅ o₅ e₅ => wp_mov fun s₆ o₆ e₆ => wp_nil ?_)
  have k₆ := ((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆
  have x15 : s₆.gpr .x15 = 0 := by rw [o₆.get .x15, o₅.get .x15, o₄.get .x15, e₃]; rfl
  refine WP.mono (count_loop (n := (s₀.gpr .x4).toNat) (by omega) (fun t s =>
      s.gpr .x10 = s₀.gpr .x3 + BitVec.ofNat 64 (4 * t) ∧
      (s.gpr .x8).toNat = (s₀.gpr .x4).toNat - t ∧ Keep [.x8, .x10] s₆ s ∧ Frame [uR s₀] s₀.mem s.mem ∧
      ∀ u < t, coeffAt s.mem (s₀.gpr .x3) u = 0)
    (fun t ht s ⟨h10, h8, hk, hf, hz⟩ => ?_)
    ⟨by rw [o₆.get .x10, e₅, o₄.get .x3, o₃.get .x3, o₂.get .x3, o₁.get .x3, Nat.mul_zero, ptr_zero],
      (by rw [e₆, o₅.get .x4, o₄.get .x4, o₃.get .x4, o₂.get .x4, o₁.get .x4, Nat.sub_zero]), Keep.refl _ _,
      by rw [k₆.mem]; exact Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩)
    fun s ⟨_, _, hk, hf, hz⟩ => ⟨hz, hf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc : (uR s₀).Contains (coeffAddr (s₀.gpr .x3) t) 4 := Offset.contains_base _ (by omega) (by omega)
    refine wp_strw ⟨by decide, by decide⟩ (by rw [h10, ptr_zero]) (by rw [hk.wr, k₆.wr, hwr]; exact ⟨_, .head _, hc⟩)
      fun s₁ h₁ => wp_addImm (by decide) fun s₂ o₂ e₂ => wp_subImm (by decide) fun s₃ o₃ e₃ => wp_nil
        ⟨⟨by rw [o₃.get .x10, e₂, h₁.gpr, h10, ptr_add, show 4 * t + 4 = 4 * (t + 1) by omega],
          by rw [e₃, o₂.get .x8, h₁.gpr]; exact count_step h8 ht,
          ((hk.trans h₁.keep).trans (o₂.keep.trans o₃.keep)).mono, ?_, fun u hu => ?_⟩, ?_⟩
    · rw [o₃.mem, o₂.mem, h₁.mem]
      exact hf.writeW (List.mem_singleton_self _) _ hc
    · rw [o₃.mem, o₂.mem, h₁.mem, coeffAt_writeW _ _ (by omega) (by omega)]
      by_cases e : t = u
      · subst e; rw [ite_eq_left rfl, hk.get .x15, x15]; rfl
      · rw [ite_eq_right e]; exact hz u (by omega)
    · rw [e₃, o₂.get .x8, h₁.gpr, count_step h8 ht]; omega
  · rw [hk.get .x9, o₆.get .x9, o₅.get .x9, e₄, o₃.get .x0, o₂.get .x0, o₁.get .x0]
  · rw [hk.get .x3, k₆.get .x3]
  · rw [hk.get .x2, o₆.get .x2, o₅.get .x2, o₄.get .x2, o₃.get .x2, e₂, o₁.get .x1, e₁]
  · rw [hk.get .x12, o₆.get .x12, o₅.get .x12, o₄.get .x12, o₃.get .x12, o₂.get .x12, e₁]
  · rw [hk.rd, k₆.rd]
  · rw [hk.wr, k₆.wr]
  · rw [hk.sp, k₆.sp]

/-! ## The hint in memory -/

/-- The words of `h` are the hint `hA` of the spec. -/
def HArr (s₀ : State) (m : Mem) (hA : Array (Vector Bool n)) : Prop :=
  hA.size = uk s₀ ∧ ∀ i < uk s₀, ∀ j < 256,
    coeffAt m (s₀.gpr .x3) (256 * i + j) = BitVec.ofNat 32 ((hA.getD i noHint)[j]!).toNat

/-- The code's state is the spec's: a hint and its index, at most `ω`, or a
failed check, and 256 in `x5`. -/
def SRel (s₀ : State) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => s.gpr .x5 = BitVec.ofNat 64 idx ∧ idx ≤ uω s₀ ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .x5 = BitVec.ofNat 64 256

/-- What stays the same from the loops on. -/
structure UCom (s₀ : State) (s : State) : Prop where
  x9 : s.gpr .x9 = s₀.gpr .x0
  x2 : s.gpr .x2 = BitVec.ofNat 64 (uω s₀)
  x15 : s.gpr .x15 = BitVec.ofNat 64 1
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [uR s₀] s₀.mem s.mem

theorem UCom.of_keep {s₀ s s' : State} (h : UCom s₀ s) {rs : List Reg} (hk : Keep rs s s')
    (hm : Frame [uR s₀] s.mem s'.mem) (h9 : Reg.x9 ∉ rs := by decide) (h2 : Reg.x2 ∉ rs := by decide)
    (h15 : Reg.x15 ∉ rs := by decide) : UCom s₀ s' :=
  ⟨(hk.gpr _ h9).trans h.x9, (hk.gpr _ h2).trans h.x2, (hk.gpr _ h15).trans h.x15, hk.rd.trans h.rd,
    hk.wr.trans h.wr, hk.sp.trans h.sp, h.frame.trans hm⟩

theorem UCom.of_only {s₀ s s' : State} (h : UCom s₀ s) {rs : List Reg} (hk : Only rs s s')
    (h9 : Reg.x9 ∉ rs := by decide) (h2 : Reg.x2 ∉ rs := by decide) (h15 : Reg.x15 ∉ rs := by decide) :
    UCom s₀ s' :=
  h.of_keep hk.keep (by rw [hk.mem]; exact Frame.refl _ _) h9 h2 h15

/-- Where the loops of polynomial `i` are. -/
structure PCom (s₀ : State) (i bound : Nat) (s : State) : Prop where
  com : UCom s₀ s
  x3 : s.gpr .x3 = s₀.gpr .x3 + BitVec.ofNat 64 (1024 * i)
  x6 : s.gpr .x6 = s₀.gpr .x0 + BitVec.ofNat 64 (uω s₀ + i)
  x7 : s.gpr .x7 = BitVec.ofNat 64 bound
  x12 : (s.gpr .x12).toNat = uk s₀ - i

theorem PCom.of_keep {s₀ s s' : State} {i bound : Nat} (h : PCom s₀ i bound s) {rs : List Reg}
    (hk : Keep rs s s') (hm : Frame [uR s₀] s.mem s'.mem)
    (hrs : ∀ r ∈ rs, r ≠ .x9 ∧ r ≠ .x2 ∧ r ≠ .x15 ∧ r ≠ .x3 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x12 := by decide) :
    PCom s₀ i bound s' :=
  ⟨h.com.of_keep hk hm (fun h' => (hrs _ h').1 rfl) (fun h' => (hrs _ h').2.1 rfl)
      (fun h' => (hrs _ h').2.2.1 rfl),
    (hk.gpr _ fun h' => (hrs _ h').2.2.2.1 rfl).trans h.x3, (hk.gpr _ fun h' => (hrs _ h').2.2.2.2.1 rfl).trans h.x6,
    (hk.gpr _ fun h' => (hrs _ h').2.2.2.2.2.1 rfl).trans h.x7,
    by rw [hk.gpr _ fun h' => (hrs _ h').2.2.2.2.2.2 rfl]; exact h.x12⟩

theorem PCom.of_only {s₀ s s' : State} {i bound : Nat} (h : PCom s₀ i bound s) {rs : List Reg}
    (hk : Only rs s s')
    (hrs : ∀ r ∈ rs, r ≠ .x9 ∧ r ≠ .x2 ∧ r ≠ .x15 ∧ r ≠ .x3 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x12 := by decide) :
    PCom s₀ i bound s' :=
  h.of_keep hk.keep (by rw [hk.mem]; exact Frame.refl _ _) hrs

include hp in
theorem harr_set {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) {i b : Nat} (hi : i < uk s₀)
    (hb : b < 256) :
    HArr s₀ (m.writeW (coeffAddr (s₀.gpr .x3) (256 * i + b)) (1 : BitVec 32)) (huSet i b hA) := by
  obtain ⟨hk4, hk8, -, -, -⟩ := up_facts hp
  refine ⟨by rw [huSet_size, hh.1], fun i' hi' j hj => ?_⟩
  rw [huSet_get (by rw [hh.1]; exact hi) (show j < n from hj)]
  by_cases e : i' = i ∧ j = b
  · obtain ⟨rfl, rfl⟩ := e
    rw [coeffAt_eq, Mem.readW_writeW_self32, ite_pos' ⟨rfl, rfl⟩]; rfl
  · rw [ite_neg' e, coeffAt_eq, Mem.readW_writeW_sep (Offset.sep _ (by
      have : 256 * i' + j ≠ 256 * i + b := fun h' => e ⟨by omega, by omega⟩
      omega) (by omega) (by omega)) (by decide), ← coeffAt_eq, hh.2 i' hi' j hj]

include hp in
theorem harr_zero {m : Mem} (hz : ∀ t < (s₀.gpr .x4).toNat, coeffAt m (s₀.gpr .x3) t = 0) :
    HArr s₀ m (Array.replicate (uk s₀) noHint) := by
  obtain ⟨-, -, -, -, hr4⟩ := up_facts hp
  refine ⟨Array.size_replicate, fun i hi j hj => ?_⟩
  rw [hz _ (by omega)]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hi, ite_true, Option.getD_some, noHint]
  rw [getElem!_pos _ j (show j < n from hj), Vector.getElem_replicate]
  rfl

include hp in
/-- A byte of `y`, unchanged by the writes to `h`. -/
theorem yByte {s : State} (hc : UCom s₀ s) {t : Nat} (ht : t < uLen s₀) :
    s.mem (s₀.gpr .x0 + BitVec.ofNat 64 t) = (uY s₀).getD t 0 := by
  have hl := (s₀.gpr .x1).isLt
  have e1 : uLen s₀ = (s₀.gpr .x1).toNat := rfl
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, ← List.getD_eq_getElem?_getD, bytesAt_getD _ _ ht]
  refine hc.frame _ fun r hr hc' => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact hp.2.2.1 _ (Offset.contains_base _ (by omega) (by omega)) hc'

include hp in
/-- Loading `y[t]` at `x9 + x5`. -/
theorem yLoad_ok {r : Reg} {t : Nat} (ht : t < uLen s₀) {s : State} (hc : UCom s₀ s)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 t) :
    WP isa (.block [.add .x .x13 .x9 .x5, .ldrb r .x13 0]) s fun s' =>
      s'.gpr r = BitVec.ofNat 64 ((uY s₀).getD t 0).toNat ∧ Only [.x13, r] s s' := by
  have hl := (s₀.gpr .x1).isLt
  have e1 : uLen s₀ = (s₀.gpr .x1).toNat := rfl
  have hrd := hp.1
  refine wp_add fun s₁ o₁ e₁ => wp_ldrb (by decide) (by rw [e₁, hc.x9, h5, ptr_zero])
    (by rw [o₁.rd, o₁.wr, hc.rd, hc.wr, hrd]; exact ⟨_, .head _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₂ o₂ e₂ => wp_nil ⟨?_, o₁.trans o₂⟩
  rw [e₂, o₁.mem, yByte hp hc ht]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_byte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := ((uY s₀).getD t 0).isLt; omega)]

/-! ## The coefficients of a polynomial -/

/-- The previous coefficient of the polynomial plus one, or 0 at its first. -/
def prevV (y : Array Byte) (first idx : Nat) : Nat := if first < idx then (y.getD (idx - 1) 0).toNat + 1 else 0

theorem huStep_eq (y : Array Byte) (i first : Nat) (hA : Array (Vector Bool n)) (idx x : Nat) :
    huStep y i first (hA, idx) x =
      if (y.getD idx 0).toNat < prevV y first idx then none
      else some (huSet i (y.getD idx 0).toNat hA, idx + 1) := by
  unfold huStep prevV
  by_cases h : first < idx
  · rw [ite_pos' h]
    by_cases h' : (y.getD (idx - 1) 0).toNat ≥ (y.getD idx 0).toNat
    · rw [ite_pos' ⟨h, h'⟩, ite_pos' (by omega)]
    · rw [ite_neg' (fun e => h' e.2), ite_neg' (by omega)]
  · rw [ite_neg' h, ite_neg' (fun e => h e.1), ite_neg' (Nat.not_lt_zero _)]

theorem huStep_idx {y : Array Byte} {i first : Nat} {st st' : Array (Vector Bool n) × Nat} {x : Nat}
    (h : huStep y i first st x = some st') : st'.2 = st.2 + 1 := by
  unfold huStep at h
  split at h
  · cases h
  · cases h; rfl

include hp in
/-- Setting coefficient `v` of polynomial `i`. -/
theorem set_ok {i bound idx v : Nat} (hi : i < uk s₀) (hv : v < 256) {hA : Array (Vector Bool n)}
    {s : State} (hP : PCom s₀ i bound s) (h5 : s.gpr .x5 = BitVec.ofNat 64 idx)
    (h10 : s.gpr .x10 = BitVec.ofNat 64 v) (hh : HArr s₀ s.mem hA) :
    WP isa (.block hbuSet) s fun s' =>
      PCom s₀ i bound s' ∧ s'.gpr .x5 = BitVec.ofNat 64 (idx + 1) ∧ s'.gpr .x11 = BitVec.ofNat 64 (v + 1) ∧
        HArr s₀ s'.mem (huSet i v hA) := by
  obtain ⟨hk4, hk8, -, -, hr4⟩ := up_facts hp
  have hwr := hp.2.1
  have ha : s₀.gpr .x3 + BitVec.ofNat 64 (1024 * i) + BitVec.ofNat 64 v <<< 2 =
      coeffAddr (s₀.gpr .x3) (256 * i + v) := by
    rw [show BitVec.ofNat 64 v <<< 2 = BitVec.ofNat 64 (4 * v) by
        apply BitVec.eq_of_toNat_eq
        rw [toNat_lsl_n (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega,
      ptr_add, coeffAddr, show 1024 * i + 4 * v = 4 * (256 * i + v) by omega]
  have hin : (uR s₀).Contains (coeffAddr (s₀.gpr .x3) (256 * i + v)) 4 :=
    Offset.contains_base _ (by omega) (by omega)
  unfold hbuSet
  refine wp_lsl (by decide) fun s₁ o₁ e₁ => wp_add fun s₂ o₂ e₂ =>
    wp_strw ⟨by decide, by decide⟩ (by rw [e₂, o₁.get .x3, e₁, hP.x3, h10, ptr_zero, ha])
      (by rw [o₂.wr, o₁.wr, hP.com.wr, hwr]; exact ⟨_, .head _, hin⟩) fun s₃ h₃ =>
    wp_addImm (by decide) fun s₄ o₄ e₄ => wp_addImm (by decide) fun s₅ o₅ e₅ => wp_nil ?_
  have k₅ := (((o₁.keep.trans o₂.keep).trans h₃.keep).trans o₄.keep).trans o₅.keep
  have m₅ : s₅.mem = s.mem.writeW (coeffAddr (s₀.gpr .x3) (256 * i + v)) (1 : BitVec 32) := by
    rw [o₅.mem, o₄.mem, h₃.mem, o₂.mem, o₁.mem, o₂.get .x15, o₁.get .x15, hP.com.x15]; rfl
  refine ⟨hP.of_keep k₅ (by rw [m₅]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hin),
    by rw [o₅.get .x5, e₄, h₃.gpr, o₂.get .x5, o₁.get .x5, h5, ofNat_succ64],
    by rw [e₅, o₄.get .x10, h₃.gpr, o₂.get .x10, o₁.get .x10, h10, ofNat_succ64], by rw [m₅]; exact harr_set hp hh hi hv⟩

/-- A failed check. -/
theorem fail_ok (s : State) :
    WP isa hbuFail s fun s' => s'.gpr .x5 = BitVec.ofNat 64 256 ∧ Only [.x5] s s' :=
  wp_movz fun _ o₁ e₁ => wp_nil ⟨by rw [e₁]; rfl, o₁⟩

/-- `x10 ← 1` if `x5 < r`, else 0. -/
theorem cmp_ok {r : Reg} (s : State) (hr : (s.gpr r).toNat < 2 ^ 63) (h5 : (s.gpr .x5).toNat < 2 ^ 63) :
    WP isa (.block [.sub .x .x10 .x5 r, .lsr .x .x10 .x10 63]) s fun s' =>
      (s'.gpr .x10 != 0) = decide ((s.gpr .x5).toNat < (s.gpr r).toNat) ∧ Only [.x10] s s' :=
  wp_sub fun _ o₁ e₁ => wp_lsr (by decide) fun _ o₂ e₂ =>
    wp_nil ⟨by rw [e₂, e₁, nz_lt h5 hr], (o₁.trans o₂).mono⟩

include hp in
/-- Coefficient `idx` of polynomial `i`, checked against the previous one. -/
theorem ucoef_ok {i bound first idx : Nat} (hi : i < uk s₀) (hfi : first ≤ idx) (hib : idx < bound) (hbω : bound ≤ uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s) (h5 : s.gpr .x5 = BitVec.ofNat 64 idx)
    (h11 : s.gpr .x11 = BitVec.ofNat 64 (prevV (uY s₀) first idx)) (hh : HArr s₀ s.mem hA) :
    WP isa hbuCoef s fun s' => PCom s₀ i bound s' ∧
      (match huStep (uY s₀) i first (hA, idx) 0 with
        | some (hA', idx') => s'.gpr .x5 = BitVec.ofNat 64 idx' ∧
          s'.gpr .x11 = BitVec.ofNat 64 (prevV (uY s₀) first idx') ∧ HArr s₀ s'.mem hA' ∧
          (s'.gpr .x10 != 0) = decide (idx' < bound)
        | none => s'.gpr .x5 = BitVec.ofNat 64 256 ∧ (s'.gpr .x10 != 0) = false) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := up_facts hp
  have hv := ((uY s₀).getD idx 0).isLt
  have hpv : prevV (uY s₀) first idx ≤ 256 := by
    unfold prevV; split
    · have := ((uY s₀).getD (idx - 1) 0).isLt; omega
    · omega
  unfold hbuCoef
  rw [show ([.add .x .x13 .x9 .x5, .ldrb .x10 .x13 0, .sub .x .x14 .x10 .x11, .lsr .x .x14 .x14 63] : List Instr) =
    [.add .x .x13 .x9 .x5, .ldrb .x10 .x13 0] ++ [.sub .x .x14 .x10 .x11, .lsr .x .x14 .x14 63] from rfl]
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (yLoad_ok hp (r := .x10) (by omega) hP.com h5) fun s₁ ⟨h10₁, o₁⟩ =>
    wp_sub fun s₂ o₂ e₂ => wp_lsr (by decide) fun s₃ o₃ e₃ => wp_nil ?_
  have k₃ := (o₁.trans o₂).trans o₃
  have hP₃ : PCom s₀ i bound s₃ := hP.of_only k₃
  have hc : (s₃.gpr .x14 != 0) = decide (((uY s₀).getD idx 0).toNat < prevV (uY s₀) first idx) := by
    rw [e₃, e₂, o₁.get .x11, h11, h10₁, nz_lt (by rw [toNat_ofNat_small (by omega)]; omega)
      (by rw [toNat_ofNat_small (by omega)]; omega), toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
  refine WP.seq (WP.ite _ (eval_nonzero s₃ .x14) (fun hf => ?_) (fun hs => ?_))
  · -- Not above the previous one: fail.
    rw [hc] at hf
    have hn : huStep (uY s₀) i first (hA, idx) 0 = none := by rw [huStep_eq, ite_pos' (of_decide_eq_true hf)]
    rw [hn]
    refine WP.mono (fail_ok s₃) fun s₄ ⟨h5₄, o₄⟩ => ?_
    refine WP.mono (cmp_ok (r := .x7) s₄ (by rw [o₄.get .x7, hP₃.x7, toNat_ofNat_small (by omega)]; omega)
      (by rw [h5₄, toNat_ofNat_small (by decide)]; decide)) fun s₅ ⟨c₅, o₅⟩ =>
      ⟨hP₃.of_only (o₄.trans o₅), by rw [o₅.get .x5, h5₄], ?_⟩
    rw [c₅, h5₄, o₄.get .x7, hP₃.x7, toNat_ofNat_small (by decide), toNat_ofNat_small (by omega)]
    exact decide_eq_false (by omega)
  · -- Set it.
    rw [hc] at hs
    have hs' := of_decide_eq_false hs
    have hn : huStep (uY s₀) i first (hA, idx) 0 =
        some (huSet i ((uY s₀).getD idx 0).toNat hA, idx + 1) := by rw [huStep_eq, ite_neg' hs']
    rw [hn]
    refine WP.mono (set_ok hp hi hv (idx := idx) (hA := hA) (hP := hP₃) (by rw [k₃.get .x5, h5]) (by rw [o₃.get .x10, o₂.get .x10, h10₁])
      (by rw [k₃.mem]; exact hh)) fun s₄ ⟨hP₄, h5₄, h11₄, hh₄⟩ => ?_
    refine WP.mono (cmp_ok (r := .x7) s₄ (by rw [hP₄.x7, toNat_ofNat_small (by omega)]; omega)
      (by rw [h5₄, toNat_ofNat_small (by omega)]; omega)) fun s₅ ⟨c₅, o₅⟩ =>
      ⟨hP₄.of_only o₅, by rw [o₅.get .x5, h5₄], ?_, by rw [o₅.mem]; exact hh₄, ?_⟩
    · rw [o₅.get .x11, h11₄, prevV, ite_pos' (by omega), Nat.add_sub_cancel]
    · rw [c₅, h5₄, hP₄.x7, toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]

/-- The state after the coefficients of a polynomial, up to the bound. -/
def SIn (s₀ : State) (bound : Nat) : Option (Array (Vector Bool n) × Nat) → State → Prop
  | some (hA, idx), s => idx = bound ∧ s.gpr .x5 = BitVec.ofNat 64 idx ∧ HArr s₀ s.mem hA
  | none, s => s.gpr .x5 = BitVec.ofNat 64 256

include hp in
/-- The coefficients of polynomial `i`, from the index `first`, up to the bound. -/
theorem coefs_ok {i bound first : Nat} (hi : i < uk s₀) (hfb : first ≤ bound) (hbω : bound ≤ uω s₀)
    {hA : Array (Vector Bool n)} {s : State} (hP : PCom s₀ i bound s) (h5 : s.gpr .x5 = BitVec.ofNat 64 first)
    (hh : HArr s₀ s.mem hA) :
    WP isa hbuCoefs s fun s' => PCom s₀ i bound s' ∧
      SIn s₀ bound (optFold (huStep (uY s₀) i first) (List.range (bound - first)) (hA, first)) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := up_facts hp
  unfold hbuCoefs
  refine WP.seq (wp_movz fun s₁ o₁ e₁ => wp_sub fun s₂ o₂ e₂ => wp_lsr (by decide) fun s₃ o₃ e₃ => wp_nil ?_)
  have k₃ := (o₁.trans o₂).trans o₃
  have hP₃ : PCom s₀ i bound s₃ := hP.of_only k₃
  have h5₃ : s₃.gpr .x5 = BitVec.ofNat 64 first := by rw [k₃.get .x5, h5]
  have hc : (s₃.gpr .x10 != 0) = decide (first < bound) := by
    rw [e₃, e₂, o₁.get .x5, o₁.get .x7, h5, hP.x7, nz_lt (by rw [toNat_ofNat_small (by omega)]; omega)
      (by rw [toNat_ofNat_small (by omega)]; omega), toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)]
  refine WP.ite _ (eval_nonzero s₃ .x10) (fun hlt => ?_) (fun hge => ?_)
  · -- The coefficients, while the index is less than the bound.
    rw [hc] at hlt
    have hlt := of_decide_eq_true hlt
    refine WP.loop (M := isa) (fun m s' => ∃ t hA' idx', m = bound - idx' ∧
        optFold (huStep (uY s₀) i first) (List.range t) (hA, first) = some (hA', idx') ∧ idx' = first + t ∧
        idx' < bound ∧ PCom s₀ i bound s' ∧ s'.gpr .x5 = BitVec.ofNat 64 idx' ∧
        s'.gpr .x11 = BitVec.ofNat 64 (prevV (uY s₀) first idx') ∧ HArr s₀ s'.mem hA')
      (fun m s' ⟨t, hA', idx', hm, hF, hidx, hlt', hP', h5', h11', hh'⟩ => ?_) _ s₃
      ⟨0, hA, first, rfl, rfl, rfl, hlt, hP₃, h5₃, by rw [o₃.get .x11, o₂.get .x11, e₁]; unfold prevV; rw [ite_neg' (Nat.lt_irrefl _)]; rfl,
        by rw [k₃.mem]; exact hh⟩
    refine WP.mono (ucoef_ok hp hi (by omega) hlt' hbω hP' h5' h11' hh') fun s'' ⟨hP'', hm''⟩ => ?_
    have hF1 : optFold (huStep (uY s₀) i first) (List.range (t + 1)) (hA, first) =
        huStep (uY s₀) i first (hA', idx') t := by rw [optFold_range_succ, hF]; rfl
    have hst : huStep (uY s₀) i first (hA', idx') t = huStep (uY s₀) i first (hA', idx') 0 := by
      rw [huStep_eq, huStep_eq]
    cases hs : huStep (uY s₀) i first (hA', idx') 0 with
    | none =>
      rw [hs] at hm''
      obtain ⟨h5'', c''⟩ := hm''
      refine .inl ⟨by rw [eval_nonzero, c''], hP'', ?_⟩
      have : optFold (huStep (uY s₀) i first) (List.range (t + 1)) (hA, first) = none := by
        rw [hF1, hst]; exact hs
      rw [optFold_range_none _ (show t + 1 ≤ bound - first by omega) this]
      exact h5''
    | some st =>
      rw [hs] at hm''
      obtain ⟨hA'', idx''⟩ := st
      obtain ⟨h5'', h11'', hh'', c''⟩ := hm''
      have hi'' : idx'' = idx' + 1 := huStep_idx hs
      have hF2 : optFold (huStep (uY s₀) i first) (List.range (t + 1)) (hA, first) = some (hA'', idx'') := by
        rw [hF1, hst]; exact hs
      by_cases e : idx'' < bound
      · refine .inr ⟨by rw [eval_nonzero, c'', decide_eq_true e], bound - idx'', by omega, t + 1, hA'', idx'', rfl,
          hF2, by omega, e, hP'', h5'', h11'', hh''⟩
      · refine .inl ⟨by rw [eval_nonzero, c'', decide_eq_false e], hP'', ?_⟩
        rw [show bound - first = t + 1 by omega, hF2]
        exact ⟨by omega, h5'', hh''⟩
  · -- No coefficient.
    rw [hc] at hge
    have hge := of_decide_eq_false hge
    refine WP.block_nil ⟨hP₃, ?_⟩
    rw [show bound - first = 0 by omega]
    exact ⟨by omega, h5₃, by rw [k₃.mem]; exact hh⟩

/-! ## A polynomial -/

/-- The spec's state after `i` polynomials. -/
abbrev huS (s₀ : State) (i : Nat) : Option (Array (Vector Bool n) × Nat) :=
  optFold (huPoly (uω s₀) (uY s₀)) (List.range i) (Array.replicate (uk s₀) noHint, 0)

/-- Before polynomial `i`. -/
structure OInv (s₀ : State) (i : Nat) (s : State) : Prop where
  com : UCom s₀ s
  x3 : s.gpr .x3 = s₀.gpr .x3 + BitVec.ofNat 64 (1024 * i)
  x6 : s.gpr .x6 = s₀.gpr .x0 + BitVec.ofNat 64 (uω s₀ + i)
  x12 : (s.gpr .x12).toNat = uk s₀ - i
  st : SRel s₀ (huS s₀ i) s

include hp in
/-- Polynomial `i`: its checks and coefficients; after a failed check, fails again. -/
theorem upolyBody_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa hbuPoly s fun s' => UCom s₀ s' ∧ s'.gpr .x3 = s.gpr .x3 ∧ s'.gpr .x6 = s.gpr .x6 ∧
      s'.gpr .x12 = s.gpr .x12 ∧ SRel s₀ (huS s₀ (i + 1)) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := up_facts hp
  have hl := (s₀.gpr .x1).isLt
  have e1 : uLen s₀ = (s₀.gpr .x1).toNat := rfl
  have hrd := hp.1
  have hsucc : huS s₀ (i + 1) = (huS s₀ i).bind fun st => huPoly (uω s₀) (uY s₀) st i := optFold_range_succ _ _ _
  unfold hbuPoly
  -- The bound.
  have hbl := ((uY s₀).getD (uω s₀ + i) 0).isLt
  refine WP.seq (wp_ldrb (by decide) (by rw [hI.x6, ptr_zero])
    (by rw [hI.com.rd, hI.com.wr, hrd]; exact ⟨_, .head _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun s₁ o₁ e₁ => wp_sub fun s₂ o₂ e₂ => wp_sub fun s₃ o₃ e₃ => wp_orr fun s₄ o₄ e₄ =>
      wp_lsr (by decide) fun s₅ o₅ e₅ => wp_nil ?_)
  have k₅ := (((o₁.trans o₂).trans o₃).trans o₄).trans o₅
  have hc₅ : UCom s₀ s₅ := hI.com.of_only k₅
  have hb : s₁.gpr .x7 = BitVec.ofNat 64 ((uY s₀).getD (uω s₀ + i) 0).toNat := by
    rw [e₁, yByte hp hI.com (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [toNat_byte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb2 : (s₁.gpr .x7).toNat = ((uY s₀).getD (uω s₀ + i) 0).toNat := by rw [hb, toNat_ofNat_small (by omega)]
  have hx5 : (s.gpr .x5).toNat ≤ 256 := by
    have := hI.st
    revert this
    cases huS s₀ i with
    | none => intro h; rw [SRel] at h; rw [h, toNat_ofNat_small (by decide)]
    | some st => obtain ⟨hA, idx⟩ := st; intro ⟨h, h', _⟩; rw [h, toNat_ofNat_small (by omega)]; omega
  have hω2 : (s₁.gpr .x2).toNat = uω s₀ := by rw [o₁.get .x2, hI.com.x2, toNat_ofNat_small (by omega)]
  have hc : (s₅.gpr .x10 != 0) =
      decide (((uY s₀).getD (uω s₀ + i) 0).toNat < (s.gpr .x5).toNat ∨ uω s₀ < ((uY s₀).getD (uω s₀ + i) 0).toNat) := by
    rw [e₅, e₄, o₃.get .x10, e₃, e₂, o₂.get .x7, o₁.get .x5, o₂.get .x2,
      nz_or (by omega) (by omega) (by omega) (by omega), hb2, hω2]
  have hkeep : ∀ {s' : State} {rs : List Reg}, Keep rs s₅ s' → Reg.x3 ∉ rs → Reg.x6 ∉ rs → Reg.x12 ∉ rs →
      s'.gpr .x3 = s.gpr .x3 ∧ s'.gpr .x6 = s.gpr .x6 ∧ s'.gpr .x12 = s.gpr .x12 := fun hk h3 h6 h12 =>
    ⟨by rw [hk.gpr _ h3, k₅.get .x3], by rw [hk.gpr _ h6, k₅.get .x6], by rw [hk.gpr _ h12, k₅.get .x12]⟩
  refine WP.ite _ (eval_nonzero s₅ .x10) (fun hf => ?_) (fun hs => ?_)
  · -- A failed check, now or before.
    rw [hc] at hf
    have hf := of_decide_eq_true hf
    refine WP.mono (fail_ok s₅) fun s₆ ⟨h5₆, o₆⟩ => ?_
    obtain ⟨k3, k6, k12⟩ := hkeep o₆.keep (by decide) (by decide) (by decide)
    refine ⟨hc₅.of_only o₆, k3, k6, k12, ?_⟩
    rw [hsucc]
    have := hI.st
    revert this
    cases huS s₀ i with
    | none => intro _; exact h5₆
    | some st =>
      obtain ⟨hA, idx⟩ := st
      intro ⟨h5, _, _⟩
      rw [h5, toNat_ofNat_small (by omega)] at hf
      simp only [Option.bind_some, huPoly]
      rw [ite_pos' hf]
      exact h5₆
  · -- The coefficients.
    rw [hc] at hs
    have hs := of_decide_eq_false hs
    have hst := hI.st
    revert hst
    cases hS : huS s₀ i with
    | none =>
      intro h5
      rw [SRel] at h5
      rw [h5, toNat_ofNat_small (by decide)] at hs
      omega
    | some st =>
      obtain ⟨hA, idx⟩ := st
      intro ⟨h5, hidx, hh⟩
      rw [h5, toNat_ofNat_small (by omega)] at hs
      have hP₅ : PCom s₀ i ((uY s₀).getD (uω s₀ + i) 0).toNat s₅ :=
        ⟨hc₅, by rw [k₅.get .x3, hI.x3], by rw [k₅.get .x6, hI.x6], by rw [o₅.get .x7, o₄.get .x7, o₃.get .x7,
          o₂.get .x7, hb], by rw [k₅.get .x12, hI.x12]⟩
      refine WP.mono (coefs_ok hp hi (first := idx) (hA := hA) (by omega) (by omega) hP₅ (by rw [k₅.get .x5, h5])
        (by rw [k₅.mem]; exact hh)) fun s₆ ⟨hP₆, hin₆⟩ => ⟨hP₆.com, by rw [hP₆.x3, hI.x3], by rw [hP₆.x6, hI.x6],
          ?_, ?_⟩
      · apply BitVec.eq_of_toNat_eq; rw [hP₆.x12, hI.x12]
      · rw [hsucc, hS]
        simp only [Option.bind_some, huPoly]
        rw [ite_neg' hs]
        revert hin₆
        cases optFold (huStep (uY s₀) i idx) (List.range (((uY s₀).getD (uω s₀ + i) 0).toNat - idx)) (hA, idx) with
        | none => exact id
        | some st => obtain ⟨hA', idx'⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨h2, by omega, h3⟩

include hp in
/-- Polynomial `i`, and the pointers and count to the next. -/
theorem upoly_ok {i : Nat} (hi : i < uk s₀) {s : State} (hI : OInv s₀ i s) :
    WP isa (.seq hbuPoly (.block [.addImm .x .x6 .x6 1, .addImm .x .x3 .x3 1024, .subImm .x .x12 .x12 1])) s
      fun s' => OInv s₀ (i + 1) s' ∧ ((s'.gpr .x12).toNat ≠ 0 ↔ i + 1 ≠ uk s₀) := by
  refine WP.seq (WP.mono (upolyBody_ok hp hi hI) fun s₁ ⟨hc₁, h3, h6, h12, st₁⟩ => ?_)
  refine wp_addImm (by decide) fun s₂ o₂ e₂ => wp_addImm (by decide) fun s₃ o₃ e₃ =>
    wp_subImm (by decide) fun s₄ o₄ e₄ => wp_nil ?_
  have k₄ := (o₂.trans o₃).trans o₄
  have c12 : (s₄.gpr .x12).toNat = uk s₀ - (i + 1) := by
    rw [e₄, o₃.get .x12, o₂.get .x12, h12]; exact count_step hI.x12 hi
  refine ⟨⟨hc₁.of_only k₄, ?_, ?_, c12, ?_⟩, by rw [c12]; omega⟩
  · rw [o₄.get .x3, e₃, o₂.get .x3, h3, hI.x3, ptr_add, show 1024 * i + 1024 = 1024 * (i + 1) by omega]
  · rw [o₄.get .x6, o₃.get .x6, e₂, h6, hI.x6, ptr_add, Nat.add_assoc]
  · revert st₁
    cases huS s₀ (i + 1) with
    | none => exact fun h => by rw [SRel] at h ⊢; rw [k₄.get .x5, h]
    | some st => obtain ⟨hA, idx⟩ := st; exact fun ⟨h1, h2, h3⟩ => ⟨by rw [k₄.get .x5, h1], h2, by rw [k₄.mem]; exact h3⟩

end

end VG.Proof.MlDsa.AArch64.Pack
