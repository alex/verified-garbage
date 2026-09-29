import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Sample
import VerifiedGarbage.Impl.MlKem.AArch64.Sample

/-!
# ML-KEM on AArch64: the loop of `SampleNTT`

Untrusted: everything here is checked by Lean. The 280 iterations of
`sampleLoop` on the SHAKE128 output `xofByte B` at `bP` compute
`sampleAfter [] (xofByte B) 280` (`Proof/MlKem/Sample.lean`) into `a`,
which starts as zeros, and return whether it has 256 coefficients
(`loop_ok`). The loop reads only the output, and writes only `a`.
-/

namespace VG.Proof.MlKem.AArch64.Sample

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

/-- What the loop needs of the state it starts in: the output of SHAKE128
of `B` at `bP`, which it may read; zeros at `aP`, which it may write. -/
structure LPre (B : List Byte) (bP aP : Addr) (s : State) : Prop where
  buf : ∀ p < 840, s.mem (bP + BitVec.ofNat 64 p) = xofByte B p
  inb : ∀ p < 840, InRegions (s.rd ++ s.wr) (bP + BitVec.ofNat 64 p) 1
  ina : ∀ i < 256, InRegions s.wr (coeffAddr aP i) 4
  disj : (⟨bP, 840⟩ : Region).Disjoint (polyRegion aP)
  zero : ∀ i < 256, coeffAt s.mem aP i = 0
  x2 : s.gpr .x2 = bP
  x3 : s.gpr .x3 = aP
  x4 : (s.gpr .x4).toNat = 256
  x5 : (s.gpr .x5).toNat = 280
  x9 : (s.gpr .x9).toNat = q
  x10 : (s.gpr .x10).toNat = 15

/-- Coefficient `i` of the list `L`, as stored. -/
def cv (L : List Zq) (i : Nat) : BitVec 32 := BitVec.ofNat 32 (L.getD i 0).val

/-- The coefficients accepted so far, `L`, stored at `aP`, with zeros after
them; the permissions, and all memory outside `a`, as in `s₀`. -/
structure Acc (aP : Addr) (s₀ : State) (L : List Zq) (u : State) : Prop where
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  sp : u.sp = s₀.sp
  len : L.length ≤ 256
  x3 : u.gpr .x3 = coeffAddr aP L.length
  x4 : (u.gpr .x4).toNat = 256 - L.length
  x9 : (u.gpr .x9).toNat = q
  coeffs : CoeffsUpTo u.mem aP L.length (cv L) fun _ => 0
  frame : Frame [polyRegion aP] s₀.mem u.mem

theorem CoeffsUpTo.congr {m : Mem} {p : Addr} {t : Nat} {G G' old : Nat → BitVec 32}
    (h : CoeffsUpTo m p t G old) (hg : ∀ i < t, G i = G' i) : CoeffsUpTo m p t G' old :=
  fun i hi => by
    rw [h i hi]
    by_cases hit : i < t
    · rw [ite_eq_left hit, ite_eq_left hit, hg i hit]
    · rw [ite_eq_right hit, ite_eq_right hit]

theorem cv_append (L : List Zq) (x : Zq) {i : Nat} (hi : i < L.length) : cv L i = cv (L ++ [x]) i := by
  simp only [cv, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem cv_last (L : List Zq) (x : Zq) : cv (L ++ [x]) L.length = BitVec.ofNat 32 x.val := by
  simp [cv]

/-- `v - q`, negative exactly when `v < q`. -/
theorem lt_q_arith {a b : BitVec 64} {v : Nat} (ha : a.toNat = v) (hv : v < 2 ^ 12)
    (hb : b.toNat = q) : ((a - b) >>> 63).toNat = if v < q then 1 else 0 := by
  rw [toNat_lsr, BitVec.toNat_sub, ha, hb]
  have hq : q = 3329 := rfl
  split <;> omega

/-- Accepting the candidate `v` in `d` if it is less than `q`. -/
theorem accept_ok {aP : Addr} {s₀ : State} (hina : ∀ i < 256, InRegions s₀.wr (coeffAddr aP i) 4)
    {L : List Zq} {u : State} (h : Acc aP s₀ L u) (hlt : L.length < 256) {d : Reg}
    (hd : d ≠ .x13 ∧ d ≠ .x14 ∧ d ≠ .x3 ∧ d ≠ .x4) {v : Nat} (hv : (u.gpr d).toNat = v)
    (hv' : v < 2 ^ 12) :
    WP isa (sampleAccept d) u fun u' =>
      Acc aP s₀ (if v < q then L ++ [ofNat v] else L) u' ∧ Keep [.x3, .x4, .x13, .x14] u u' := by
  have hq : q = 3329 := rfl
  refine WP.seq (wp_sub fun u₁ h₁ e₁ => wp_lsr (by decide) fun u₂ h₂ e₂ => wp_nil ?_)
  have k₂ := (h₁.keep.trans h₂.keep).mono (rs' := [.x3, .x4, .x13, .x14]) (by decide)
  have v14 : (u₂.gpr .x14).toNat = if v < q then 1 else 0 := by
    rw [e₂, e₁]
    exact lt_q_arith hv hv' h.x9
  have a₂ : Acc aP s₀ L u₂ :=
    ⟨by rw [k₂.rd, h.rd], by rw [k₂.wr, h.wr], by rw [k₂.sp, h.sp], h.len,
      by rw [h₂.get .x3, h₁.get .x3, h.x3], by rw [h₂.get .x4, h₁.get .x4, h.x4],
      by rw [h₂.get .x9, h₁.get .x9, h.x9], by rw [h₂.mem, h₁.mem]; exact h.coeffs,
      by rw [h₂.mem, h₁.mem]; exact h.frame⟩
  refine WP.ite (u₂.gpr .x14 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, v14] at hz
    refine wp_nil ⟨?_, k₂⟩
    rw [ite_eq_right (by intro hvq; rw [ite_eq_left hvq] at hz; cases hz)]
    exact a₂
  · rw [eq_zero_iff, decide_eq_false_iff_not, v14] at hz
    have hvq : v < q := by by_contra hn; rw [ite_eq_right hn] at hz; exact hz rfl
    rw [ite_eq_left hvq]
    refine wp_strw (a := coeffAddr aP L.length) (by decide) (by rw [a₂.x3, ptr_zero])
      (by rw [a₂.wr]; exact hina _ hlt) fun u₃ h₃ =>
      wp_addImm (by decide) fun u₄ h₄ e₄ => wp_subImm (by decide) fun u₅ h₅ e₅ => wp_nil ?_
    have k₅ := ((h₃.keep.trans h₄.keep).trans h₅.keep).mono (rs' := [.x3, .x4, .x13, .x14]) (by decide)
    have c4 : (u₄.gpr .x4).toNat = 256 - L.length := by rw [h₄.get .x4, h₃.gpr, a₂.x4]
    have m₅ : u₅.mem = u₂.mem.writeW (coeffAddr aP L.length) ((u₂.gpr d).setWidth 32) := by
      rw [h₅.mem, h₄.mem, h₃.mem]
    have dv : (u₂.gpr d).toNat = v := by
      rw [h₂.get d (by simpa using hd.2.1), h₁.get d (by simpa using hd.1), hv]
    refine ⟨⟨by rw [k₅.rd, a₂.rd], by rw [k₅.wr, a₂.wr], by rw [k₅.sp, a₂.sp],
      by simp only [List.length_append, List.length_singleton]; omega, ?_, ?_,
      by rw [k₅.get .x9, a₂.x9], ?_, ?_⟩, k₂.trans k₅ |>.mono⟩
    · rw [h₅.get .x3, e₄, h₃.gpr, a₂.x3, List.length_append, List.length_singleton, coeffAddr,
        coeffAddr, ptr_next]
    · rw [e₅, toNat_sub_n (by rw [c4]; simp; omega), c4, List.length_append, List.length_singleton]
      simp
      omega
    · rw [m₅, List.length_append, List.length_singleton]
      refine CoeffsUpTo.write (CoeffsUpTo.congr a₂.coeffs fun i hi => cv_append L (ofNat v) hi) hlt ?_
      rw [cv_last, setWidth32_of_toNat dv, val_ofNat, Nat.mod_eq_of_lt hvq]
    · rw [m₅]
      exact a₂.frame.writeW (List.mem_singleton_self _) _
        (coeff_contains _ (show L.length < n from hlt))

/-! ## One iteration -/

/-- The first candidate of chunk `t`. -/
abbrev d₁ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t)).toNat + 256 * ((xofByte B (3 * t + 1)).toNat % 16)

/-- The second candidate of chunk `t`. -/
abbrev d₂ (B : List Byte) (t : Nat) : Nat :=
  (xofByte B (3 * t + 1)).toNat / 16 + 16 * (xofByte B (3 * t + 2)).toNat

/-- The coefficients accepted after `t` iterations. -/
abbrev LA (B : List Byte) (t : Nat) : List Zq := sampleAfter [] (xofByte B) t

/-- The registers the loop changes. -/
abbrev lRegs : List Reg := [.x2, .x3, .x4, .x5, .x6, .x7, .x8, .x11, .x12, .x13, .x14]

/-- After `t` iterations. -/
structure Inv (B : List Byte) (bP aP : Addr) (s₀ : State) (t : Nat) (u : State) : Prop where
  acc : Acc aP s₀ (LA B t) u
  keep : Keep lRegs s₀ u
  x2 : u.gpr .x2 = bP + BitVec.ofNat 64 (3 * t)
  x5 : (u.gpr .x5).toNat = 280 - t
  x10 : (u.gpr .x10).toNat = 15

theorem sampleStepCap_eq (L : List Zq) (c₀ c₁ c₂ : Byte) (hL : L.length ≠ n) :
    sampleStepCap L c₀ c₁ c₂ =
      let a := if c₀.toNat + 256 * (c₁.toNat % 16) < q
        then L ++ [ofNat (c₀.toNat + 256 * (c₁.toNat % 16))] else L
      if c₁.toNat / 16 + 16 * c₂.toNat < q ∧ a.length < n
        then a ++ [ofNat (c₁.toNat / 16 + 16 * c₂.toNat)] else a := by
  unfold sampleStepCap sampleStep
  rw [ite_eq_right hL]

theorem acc_keep {aP : Addr} {s₀ : State} {L : List Zq} {u u' : State} (h : Acc aP s₀ L u)
    {rs : List Reg} (hk : Keep rs u u') (hm : u'.mem = u.mem) (h3 : Reg.x3 ∉ rs := by decide)
    (h4 : Reg.x4 ∉ rs := by decide) (h9 : Reg.x9 ∉ rs := by decide) : Acc aP s₀ L u' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], h.len, by rw [hk.get .x3 h3, h.x3],
    by rw [hk.get .x4 h4, h.x4], by rw [hk.get .x9 h9, h.x9], by rw [hm]; exact h.coeffs,
    by rw [hm]; exact h.frame⟩

/-- The candidates of chunk `t`. -/
theorem chunk_ok {B : List Byte} {bP aP : Addr} {s₀ : State} (hp : LPre B bP aP s₀) {t : Nat}
    (ht : t < 280) {u : State} (h : Inv B bP aP s₀ t u) :
    WP isa (.block sampleChunk) u fun u' => Acc aP s₀ (LA B t) u' ∧
      Keep [.x2, .x5, .x6, .x7, .x8, .x11, .x12, .x13] u u' ∧
      u'.gpr .x2 = bP + BitVec.ofNat 64 (3 * (t + 1)) ∧ (u'.gpr .x5).toNat = 280 - (t + 1) ∧
      (u'.gpr .x11).toNat = d₁ B t ∧ (u'.gpr .x12).toNat = d₂ B t := by
  have hin : ∀ p < 840, InRegions (u.rd ++ u.wr) (bP + BitVec.ofNat 64 p) 1 := fun p hp' => by
    rw [h.acc.rd, h.acc.wr]; exact hp.inb p hp'
  have hb : ∀ p < 840, (u.mem (bP + BitVec.ofNat 64 p)).toNat = (xofByte B p).toNat := fun p hp' => by
    rw [byte_frame h.acc.frame (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj) (by decide) hp', hp.buf p hp']
  have a : ∀ r, u.gpr .x2 + BitVec.ofNat 64 r = bP + BitVec.ofNat 64 (3 * t + r) := fun r => by
    rw [h.x2, ptr_add]
  refine wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 0)) (by decide) (a 0) (hin _ (by omega))
    fun u₁ h₁ e₁ => ?_
  refine wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 1)) (by decide) (by rw [h₁.get .x2, a])
    (by rw [h₁.rd, h₁.wr]; exact hin _ (by omega)) fun u₂ h₂ e₂ => ?_
  refine wp_ldrb (a := bP + BitVec.ofNat 64 (3 * t + 2)) (by decide)
    (by rw [h₂.get .x2, h₁.get .x2, a]) (by rw [h₂.rd, h₂.wr, h₁.rd, h₁.wr]; exact hin _ (by omega))
    fun u₃ h₃ e₃ => ?_
  refine wp_addImm (by decide) fun u₄ h₄ e₄ => wp_subImm (by decide) fun u₅ h₅ e₅ =>
    wp_and fun u₆ h₆ e₆ => wp_lsl (by decide) fun u₇ h₇ e₇ => wp_add fun u₈ h₈ e₈ =>
    wp_lsr (by decide) fun u₉ h₉ e₉ => wp_lsl (by decide) fun u₁₀ h₁₀ e₁₀ =>
    wp_add fun u₁₁ h₁₁ e₁₁ => wp_nil ?_
  have l0 := (xofByte B (3 * t)).isLt
  have l1 := (xofByte B (3 * t + 1)).isLt
  have l2 := (xofByte B (3 * t + 2)).isLt
  have v6 : (u₅.gpr .x6).toNat = (xofByte B (3 * t)).toNat := by
    rw [h₅.get .x6, h₄.get .x6, h₃.get .x6, h₂.get .x6, e₁, toNat_byte, Nat.add_zero, hb _ (by omega)]
  have v7 : (u₅.gpr .x7).toNat = (xofByte B (3 * t + 1)).toNat := by
    rw [h₅.get .x7, h₄.get .x7, h₃.get .x7, e₂, toNat_byte, h₁.mem, hb _ (by omega)]
  have v8 : (u₅.gpr .x8).toNat = (xofByte B (3 * t + 2)).toNat := by
    rw [h₅.get .x8, h₄.get .x8, e₃, toNat_byte, h₂.mem, h₁.mem, hb _ (by omega)]
  have k₁₁ := (((((((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans
    h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep).trans h₁₀.keep).trans h₁₁.keep
  have m₁₁ : u₁₁.mem = u.mem := by
    rw [h₁₁.mem, h₁₀.mem, h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨acc_keep h.acc (k₁₁.mono (rs' := [.x2, .x5, .x6, .x7, .x8, .x11, .x12, .x13]) (by decide))
    m₁₁, k₁₁.mono (by decide), ?_, ?_, ?_, ?_⟩
  · rw [h₁₁.get .x2, h₁₀.get .x2, h₉.get .x2, h₈.get .x2, h₇.get .x2, h₆.get .x2, h₅.get .x2, e₄,
      h₃.get .x2, h₂.get .x2, h₁.get .x2, h.x2, ptr_add, show 3 * t + 3 = 3 * (t + 1) by omega]
  · have c5 : (u₄.gpr .x5).toNat = 280 - t := by
      rw [h₄.get .x5, h₃.get .x5, h₂.get .x5, h₁.get .x5, h.x5]
    rw [h₁₁.get .x5, h₁₀.get .x5, h₉.get .x5, h₈.get .x5, h₇.get .x5, h₆.get .x5, e₅,
      toNat_sub_n (by rw [c5]; simp; omega), c5]
    simp
    omega
  · have c6 : (u₆.gpr .x11).toNat = (xofByte B (3 * t + 1)).toNat % 16 := by
      rw [e₆, toNat_and_mask _ _ (k := 4) (by
        rw [h₅.get .x10, h₄.get .x10, h₃.get .x10, h₂.get .x10, h₁.get .x10, h.x10]), v7]
    have c7 : (u₇.gpr .x11).toNat = (xofByte B (3 * t + 1)).toNat % 16 * 256 := by
      rw [e₇, toNat_lsl_n (by rw [c6]; omega), c6]
    rw [h₁₁.get .x11, h₁₀.get .x11, h₉.get .x11, e₈,
      toNat_add_n (by rw [c7, h₇.get .x6, h₆.get .x6, v6]; omega), c7, h₇.get .x6, h₆.get .x6, v6]
    simp only [d₁]
    omega
  · have c9 : (u₉.gpr .x12).toNat = (xofByte B (3 * t + 1)).toNat / 16 := by
      rw [e₉, toNat_lsr, h₈.get .x7, h₇.get .x7, h₆.get .x7, v7]
    have c10 : (u₁₀.gpr .x13).toNat = (xofByte B (3 * t + 2)).toNat * 16 := by
      rw [e₁₀, toNat_lsl_n (by rw [h₉.get .x8, h₈.get .x8, h₇.get .x8, h₆.get .x8, v8]; omega),
        h₉.get .x8, h₈.get .x8, h₇.get .x8, h₆.get .x8, v8]
    rw [e₁₁, toNat_add_n (by rw [h₁₀.get .x12, c9, c10]; omega), h₁₀.get .x12, c9, c10]
    simp only [d₂]
    omega

/-- Whether the candidates are accepted: nothing once there are 256
coefficients. -/
theorem tail_ok {aP : Addr} {s₀ : State} (hina : ∀ i < 256, InRegions s₀.wr (coeffAddr aP i) 4)
    {L : List Zq} {u : State} (h : Acc aP s₀ L u) {c₀ c₁ c₂ : Byte}
    (h11 : (u.gpr .x11).toNat = c₀.toNat + 256 * (c₁.toNat % 16))
    (h12 : (u.gpr .x12).toNat = c₁.toNat / 16 + 16 * c₂.toNat) :
    WP isa (.ite (.zero .x .x4) (.block [])
      (.seq (sampleAccept .x11) (.ite (.zero .x .x4) (.block []) (sampleAccept .x12)))) u
      fun u' => Acc aP s₀ (sampleStepCap L c₀ c₁ c₂) u' ∧ Keep [.x3, .x4, .x13, .x14] u u' := by
  have l0 := c₀.isLt
  have l1 := c₁.isLt
  have l2 := c₂.isLt
  have hn : n = 256 := rfl
  have hL := h.len
  refine WP.ite (u.gpr .x4 == 0) (eval_zero _ _) (fun hz => ?_) (fun hz => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, h.x4] at hz
    rw [sampleStepCap_full (by omega)]
    exact wp_nil ⟨h, Keep.refl _ _⟩
  rw [eq_zero_iff, decide_eq_false_iff_not, h.x4] at hz
  rw [sampleStepCap_eq L c₀ c₁ c₂ (by omega)]
  refine WP.seq (WP.mono (accept_ok hina h (by omega) (d := .x11) (by decide) h11 (by omega))
    fun u₂ ⟨a₂, k₂⟩ => ?_)
  have hl1 := a₂.len
  refine WP.ite (u₂.gpr .x4 == 0) (eval_zero _ _) (fun hz' => ?_) (fun hz' => ?_)
  · rw [eq_zero_iff, decide_eq_true_eq, a₂.x4] at hz'
    dsimp only
    rw [ite_eq_right (fun hc => by omega)]
    exact wp_nil ⟨a₂, k₂⟩
  · rw [eq_zero_iff, decide_eq_false_iff_not, a₂.x4] at hz'
    refine WP.mono (accept_ok hina a₂ (by omega) (d := .x12) (v := c₁.toNat / 16 + 16 * c₂.toNat)
      (by decide)
      (by rw [k₂.get .x12]; exact h12) (by omega)) fun u₃ ⟨a₃, k₃⟩ => ⟨?_, (k₂.trans k₃).mono⟩
    dsimp only
    by_cases hd : c₁.toNat / 16 + 16 * c₂.toNat < q
    · rw [ite_eq_left ⟨hd, by omega⟩]; rw [ite_eq_left hd] at a₃; exact a₃
    · rw [ite_eq_right (fun hc => hd hc.1)]; rw [ite_eq_right hd] at a₃; exact a₃

/-- One iteration. -/
theorem body_ok {B : List Byte} {bP aP : Addr} {s₀ : State} (hp : LPre B bP aP s₀) {t : Nat}
    (ht : t < 280) {u : State} (h : Inv B bP aP s₀ t u) :
    WP isa sampleBody u fun u' =>
      Inv B bP aP s₀ (t + 1) u' ∧ ((u'.gpr .x5).toNat ≠ 0 ↔ t + 1 ≠ 280) := by
  refine WP.seq (WP.mono (chunk_ok hp ht h) fun u₁ ⟨a₁, k₁, x2₁, x5₁, x11₁, x12₁⟩ =>
    WP.mono (tail_ok hp.ina a₁ x11₁ x12₁) fun u' ⟨a', k'⟩ => ?_)
  have x5' : (u'.gpr .x5).toNat = 280 - (t + 1) := by rw [k'.get .x5, x5₁]
  refine ⟨⟨a', ((h.keep.trans k₁).trans k').mono (by decide), by rw [k'.get .x2, x2₁], x5',
    by rw [k'.get .x10, k₁.get .x10, h.x10]⟩, by rw [x5']; omega⟩

/-! ## The loop -/

theorem cv_toPoly {L : List Zq} {i : Nat} (hi : i < 256) :
    cv L i = BitVec.ofNat 32 ((toPoly L)[i]!).val := by
  simp [cv, toPoly, hi]

/-- The loop's result: 1 and `SampleNTT` at `a`, or 0 and failure; `a` is
reduced either way. -/
def Res (B : List Byte) (aP : Addr) (u : State) : Prop :=
  Reduced u.mem aP ∧ ((u.gpr .x0 = 1 ∧ PolyIs u.mem aP (toPoly (LA B 280)) ∧
      sampleNTT 280 B = some (toPoly (LA B 280))) ∨
    (u.gpr .x0 = 0 ∧ sampleNTT 280 B = none))

theorem reduced_of_coeffs {m : Mem} {p : Addr} {L : List Zq} (h : CoeffsUpTo m p L.length (cv L) fun _ => 0) :
    Reduced m p := fun i hi => by
  rw [h i hi]
  split
  · simp only [cv, BitVec.toNat_ofNat]
    have := val_lt (L.getD i 0)
    have hq : q = 3329 := rfl
    omega
  · show (0 : BitVec 32).toNat < q
    decide

theorem loop_ok {B : List Byte} {bP aP : Addr} {s₀ : State} (hp : LPre B bP aP s₀) :
    WP isa sampleLoop s₀ fun u => Keep (.x0 :: lRegs) s₀ u ∧ Frame [polyRegion aP] s₀.mem u.mem ∧
      Res B aP u := by
  have l0 : (LA B 0).length = 0 := rfl
  have i₀ : Inv B bP aP s₀ 0 s₀ := by
    refine ⟨⟨rfl, rfl, rfl, by rw [l0]; omega, by rw [hp.x3, l0, coeffAddr, Nat.mul_zero, ptr_zero],
      by rw [hp.x4, l0], hp.x9, fun i hi => ?_, Frame.refl _ _⟩, Keep.refl _ _,
      by rw [hp.x2, Nat.mul_zero, ptr_zero], by rw [hp.x5], hp.x10⟩
    rw [hp.zero i hi, l0, ite_eq_right (Nat.not_lt_zero i)]
  refine WP.seq (WP.mono (count_loop (by decide) (Inv B bP aP s₀) (fun t ht u h => body_ok hp ht h) i₀)
    fun u h => ?_)
  refine wp_subImm (by decide) fun u₁ h₁ e₁ => wp_lsr (by decide) fun u₂ h₂ e₂ => wp_nil ?_
  have hL := h.acc.len
  have c4 := h.acc.x4
  refine ⟨((h.keep.trans (h₁.keep.trans h₂.keep))).mono (by decide), by
    rw [h₂.mem, h₁.mem]; exact h.acc.frame, ?_⟩
  have v0 : (u₂.gpr .x0).toNat = if (LA B 280).length = 256 then 1 else 0 := by
    rw [e₂, toNat_lsr, e₁, BitVec.toNat_sub, c4]
    simp only [BitVec.toNat_ofNat]
    split <;> omega
  refine ⟨by rw [h₂.mem, h₁.mem]; exact reduced_of_coeffs h.acc.coeffs, ?_⟩
  by_cases hf : (LA B 280).length = 256
  · rw [ite_eq_left hf] at v0
    refine .inl ⟨BitVec.eq_of_toNat_eq (by rw [v0]; rfl), ?_, sampleNTT_of_full (Nat.le_refl _) hf⟩
    rw [h₂.mem, h₁.mem]
    have hc := h.acc.coeffs
    rw [hf] at hc
    exact CoeffsUpTo.polyIs hc fun i hi => cv_toPoly hi
  · rw [ite_eq_right hf] at v0
    exact .inr ⟨BitVec.eq_of_toNat_eq (by rw [v0]; rfl), sampleNTT_none hf⟩

end VG.Proof.MlKem.AArch64.Sample
