import VerifiedGarbage.Proof.MlDsa.AArch64.Sample.RejNttLoop
import VerifiedGarbage.Proof.MlDsa.Sample.HalfByte
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded

/-!
# ML-DSA on AArch64: the loop of `vg_mldsa_rej_bounded_poly`

The coefficient of a half-byte, computed without a branch (`rbVal`), is the
one of `CoeffFromHalfByte`, modulo `q`, for every half-byte it accepts
(`rbF_eq`, by evaluation); so a try does what `hbTry` does (`try_ok`), storing
a coefficient either way and counting it only if it is accepted, and an
iteration what `rbStep` does (`step_ok`). The loop reads only the output, and
writes only `a`.
-/

namespace VG.Proof.MlDsa.AArch64.Sample.RejBounded

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_strw wp_ldrb wp_sub
  wp_add wp_lsr wp_lsl wp_and wp_madd ptr_zero ptr_add toNat_sub_n toNat_add_n toNat_lsl_n toNat_and_mask
  toNat_byte toNat_lsr count_loop eval_zero eq_zero_iff)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov csub)
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.RejNtt (lt_bit movQ_ok q_eq stored_past)
open VG.Spec.MlDsa (coeffAt Zq q ofInt)

/-! ## The coefficient of a half-byte -/

/-- `x - k`, plus `k` if that is negative, as `csub` computes it. -/
def csubF (k x : BitVec 64) : BitVec 64 := (x - k) + ((x - k) >>> 63) * k

/-- `(η - x) mod q`, as the end of `rbVal` computes it. -/
def etaF (η x : BitVec 64) : BitVec 64 := (η - x) + ((η - x) >>> 63) * BitVec.ofNat 64 q

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 64 → BitVec 64
  | 2, x => etaF 2 (csubF 5 (csubF 10 x))
  | _, x => etaF 4 x

theorem rbF_eq2 : ∀ b < 15, (rbF 2 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, (rbF 4 (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbB η) :
    (rbF η (BitVec.ofNat 64 b)).setWidth 32 = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact rbF_eq2 b hb
  · exact rbF_eq4 b hb

/-- The constants the loop keeps in registers. -/
structure Consts (η : Nat) (u : State) : Prop where
  x9 : u.gpr .x9 = BitVec.ofNat 64 q
  x10 : u.gpr .x10 = BitVec.ofNat 64 η
  x11 : u.gpr .x11 = BitVec.ofNat 64 15
  x15 : u.gpr .x15 = BitVec.ofNat 64 (rbB η)
  x16 : u.gpr .x16 = BitVec.ofNat 64 10
  x17 : u.gpr .x17 = BitVec.ofNat 64 5

theorem Consts.keep {η : Nat} {u u' : State} (h : Consts η u) {rs : List Reg} (hk : Keep rs u u')
    (hr : ∀ r ∈ rs, r ∉ [Reg.x9, .x10, .x11, .x15, .x16, .x17] := by decide) : Consts η u' :=
  ⟨by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x9], by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x10],
    by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x11], by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x15],
    by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x16], by rw [hk.gpr _ fun h' => hr _ h' (by simp), h.x17]⟩

theorem val_ok {η : Nat} (hη : η = 2 ∨ η = 4) {u : State} (hc : Consts η u) :
    WP isa (.block (rbVal η)) u fun u' => Only [.x13, .x14] u u' ∧ u'.gpr .x13 = rbF η (u.gpr .x7) := by
  rcases hη with rfl | rfl
  · simp only [rbVal, csub, List.cons_append, List.nil_append]
    refine wp_mov fun u₁ o₁ e₁ => wp_sub fun u₂ o₂ e₂ => wp_lsr (by decide) fun u₃ o₃ e₃ =>
      wp_madd fun u₄ o₄ e₄ => wp_sub fun u₅ o₅ e₅ => wp_lsr (by decide) fun u₆ o₆ e₆ =>
      wp_madd fun u₇ o₇ e₇ => wp_sub fun u₈ o₈ e₈ => wp_lsr (by decide) fun u₉ o₉ e₉ =>
      wp_madd fun u₁₀ o₁₀ e₁₀ => wp_nil ⟨(((((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans
        o₇).trans o₈).trans o₉).trans o₁₀).mono, ?_⟩
    have a2 : u₂.gpr .x13 = u.gpr .x7 - BitVec.ofNat 64 10 := by rw [e₂, e₁, o₁.get .x16, hc.x16]
    have a4 : u₄.gpr .x13 = csubF (BitVec.ofNat 64 10) (u.gpr .x7) := by
      rw [e₄, o₃.get .x13, e₃, a2, o₃.get .x16, o₂.get .x16, o₁.get .x16, hc.x16]; rfl
    have a5 : u₅.gpr .x13 = csubF (BitVec.ofNat 64 10) (u.gpr .x7) - BitVec.ofNat 64 5 := by
      rw [e₅, a4, o₄.get .x17, o₃.get .x17, o₂.get .x17, o₁.get .x17, hc.x17]
    have a7 : u₇.gpr .x13 = csubF (BitVec.ofNat 64 5) (csubF (BitVec.ofNat 64 10) (u.gpr .x7)) := by
      rw [e₇, o₆.get .x13, e₆, a5, o₆.get .x17, o₅.get .x17, o₄.get .x17, o₃.get .x17, o₂.get .x17,
        o₁.get .x17, hc.x17]; rfl
    have a8 : u₈.gpr .x13 = BitVec.ofNat 64 2 - csubF (BitVec.ofNat 64 5) (csubF (BitVec.ofNat 64 10) (u.gpr .x7)) := by
      rw [e₈, a7, o₇.get .x10, o₆.get .x10, o₅.get .x10, o₄.get .x10, o₃.get .x10, o₂.get .x10, o₁.get .x10,
        hc.x10]
    rw [e₁₀, o₉.get .x13, e₉, a8, o₉.get .x9, o₈.get .x9, o₇.get .x9, o₆.get .x9, o₅.get .x9, o₄.get .x9,
      o₃.get .x9, o₂.get .x9, o₁.get .x9, hc.x9]; rfl
  · simp only [rbVal]
    refine wp_sub fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => wp_madd fun u₃ o₃ e₃ =>
      wp_nil ⟨((o₁.trans o₂).trans o₃).mono, ?_⟩
    rw [e₃, o₂.get .x13, e₂, e₁, o₂.get .x9, o₁.get .x9, hc.x9, hc.x10]; rfl

theorem rbB_le {η : Nat} : rbB η ≤ 15 := by unfold rbB; split <;> omega

theorem hbTry_length' {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    (hbTry η L b).length = L.length + if b < rbB η then 1 else 0 := by
  rw [hbTry_eq hη]; split <;> simp

/-- A try of the half-byte `b` in `x7`: what `hbTry` does, the coefficient
stored as coefficient `j` either way. -/
theorem try_ok {η : Nat} (hη : η = 2 ∨ η = 4) {aP : Addr} {L : List Zq} {b : Nat} (hb : b < 16) {u : State}
    (hc : Consts η u) (h7 : u.gpr .x7 = BitVec.ofNat 64 b) (h3 : u.gpr .x3 = coeffAddr aP L.length)
    (h4 : (u.gpr .x4).toNat = 256 - L.length) (hl : L.length < 256) (hst : Stored u.mem aP L)
    (hw : InRegions u.wr (coeffAddr aP L.length) 4) :
    WP isa (.block (rbTry η)) u fun u' => Keep [.x3, .x4, .x8, .x12, .x13, .x14] u u' ∧
      Frame [polyR aP] u.mem u'.mem ∧ u'.gpr .x3 = coeffAddr aP (hbTry η L b).length ∧
      (u'.gpr .x4).toNat = 256 - (hbTry η L b).length ∧ Stored u'.mem aP (hbTry η L b) := by
  unfold rbTry
  refine wp_sub fun u₁ o₁ e₁ => wp_lsr (by decide) fun u₂ o₂ e₂ => ?_
  have v12 : (u₂.gpr .x12).toNat = if b < rbB η then 1 else 0 := by
    rw [e₂, e₁]
    exact lt_bit (by rw [h7, BitVec.toNat_ofNat]; omega) (by rw [hc.x15, BitVec.toNat_ofNat]; have := @rbB_le η; omega)
      (by omega) (by have := @rbB_le η; omega)
  have hc₂ : Consts η u₂ := hc.keep (o₁.keep.trans o₂.keep)
  rw [List.append_eq, List.append_eq, List.nil_append, WP.block_append_iff]
  refine WP.mono (val_ok hη hc₂) fun u₃ ⟨o₃, e₃⟩ => ?_
  have x7 : u₂.gpr .x7 = BitVec.ofNat 64 b := by rw [o₂.get .x7, o₁.get .x7, h7]
  rw [x7] at e₃
  refine wp_strw (a := coeffAddr aP L.length) (by decide)
    (by rw [o₃.get .x3, o₂.get .x3, o₁.get .x3, h3, ptr_zero]) (by rw [o₃.wr, o₂.wr, o₁.wr]; exact hw)
    fun u₄ o₄ => wp_lsl (by decide) fun u₅ o₅ e₅ => wp_add fun u₆ o₆ e₆ => wp_sub fun u₇ o₇ e₇ => wp_nil ?_
  have k₇ := (((((o₁.keep.trans o₂.keep).trans o₃.keep).trans o₄.keep).trans o₅.keep).trans o₆.keep).trans
    o₇.keep
  have m₇ : u₇.mem = u.mem.writeW (coeffAddr aP L.length) ((rbF η (BitVec.ofNat 64 b)).setWidth 32) := by
    rw [o₇.mem, o₆.mem, o₅.mem, o₄.mem, e₃, o₃.mem, o₂.mem, o₁.mem]
  have x12 : (u₆.gpr .x12).toNat = if b < rbB η then 1 else 0 := by
    rw [o₆.get .x12, o₅.get .x12, o₄.gpr, o₃.get .x12, v12]
  have x14 : u₅.gpr .x14 = BitVec.ofNat 64 (4 * if b < rbB η then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    have c12 : (u₄.gpr .x12).toNat = if b < rbB η then 1 else 0 := by rw [o₄.gpr, o₃.get .x12, v12]
    have hl' : (u₄.gpr .x12).toNat * 2 ^ 2 < 2 ^ 64 := by rw [c12]; split <;> decide
    rw [e₅, toNat_lsl_n hl', c12, BitVec.toNat_ofNat]
    split <;> decide
  have c4 : (u₆.gpr .x4).toNat = 256 - L.length := by
    rw [o₆.get .x4, o₅.get .x4, o₄.gpr, o₃.get .x4, o₂.get .x4, o₁.get .x4, h4]
  refine ⟨k₇.mono, ?_, ?_, ?_, ?_⟩
  · rw [m₇]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (coeff_contains _ hl)
  · rw [o₇.get .x3, e₆, x14, o₅.get .x3, o₄.gpr, o₃.get .x3, o₂.get .x3, o₁.get .x3, h3, coeffAddr, coeffAddr,
      ptr_add, hbTry_length' hη, Nat.mul_add]
  · have hx : (u₆.gpr .x12).toNat ≤ (u₆.gpr .x4).toNat := by rw [x12, c4]; split <;> omega
    rw [e₇, toNat_sub_n hx, c4, x12, hbTry_length' hη]
    omega
  · rw [m₇, hbTry_eq hη]
    split
    · rename_i hr
      rw [rbF_eq hη hr]; exact stored_snoc hst hl _
    · exact stored_past hst (Nat.le_refl _) hl _

end VG.Proof.MlDsa.AArch64.Sample.RejBounded
