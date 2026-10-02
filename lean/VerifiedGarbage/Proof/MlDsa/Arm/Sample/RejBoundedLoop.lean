import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.Arm.Sample.RejBounded

/-!
# ML-DSA on 32-bit ARM: the loop of `vg_mldsa_rej_bounded_poly`

The coefficient of an accepted half-byte, computed without a branch (`rbVal`),
is the one of `CoeffFromHalfByte`, modulo `q` (`rbF_eq`, by evaluation on the
accepted half-bytes); so a try does what `hbTry` does (`try_ok`, from its
pieces `tsgn_ok` and `acc_ok`, which the proof of constant time reuses), and
an iteration what `rbStep` does (`body_ok`). Between the pieces,
`Base` holds: the environment, the XOF output, the pointer `r0` to the byte of
iteration `t`, the count `r3` and the coefficients `L` stored, `j = |L|` in
`r2`.
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne)
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold coeffAddr Stored stored_nil zw ifT ifF hbTry_length
  halfByteOk_le rbFold_snoc rbFold_length_le)
open VG.Spec.MlDsa (Zq q ofInt coeffFromHalfByte halfByteOk)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficient of a half-byte -/

/-- `x - 10` if `10 ≤ x`, as `csub 10` computes it. -/
def csubF10 (x : BitVec 32) : BitVec 32 := x - 10#32 + (x - 10#32) >>> 31 <<< 3 + (x - 10#32) >>> 31 <<< 1

/-- `x - 5` if `5 ≤ x`, as `csub 5` computes it. -/
def csubF5 (x : BitVec 32) : BitVec 32 := x - 5#32 + (x - 5#32) >>> 31 <<< 2 + (x - 5#32) >>> 31

/-- `x + q` if `x` is negative, as `addQNeg` computes it. -/
def aqF (x : BitVec 32) : BitVec 32 := x + x >>> 31 + x >>> 31 <<< 23 - x >>> 31 <<< 13

/-- What `rbVal η` computes of the half-byte `x`. -/
def rbF : Nat → BitVec 32 → BitVec 32
  | 2, x => aqF (2 - csubF5 (csubF10 x))
  | _, x => aqF (4 - x)

/-- The coefficient of an accepted half-byte. -/
def rbC (η b : Nat) : Int := if η = 2 then 2 - (b % 5 : Nat) else 4 - b

theorem coeffFromHalfByte_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    coeffFromHalfByte η b = if b < rbBound η then some (rbC η b) else none := by
  rcases hη with rfl | rfl <;> simp [coeffFromHalfByte, rbBound, rbC]

theorem rbF_eq2 : ∀ b < 15, rbF 2 (BitVec.ofNat 32 b) = zw (ofInt (rbC 2 b)) := by decide

theorem rbF_eq4 : ∀ b < 9, rbF 4 (BitVec.ofNat 32 b) = zw (ofInt (rbC 4 b)) := by decide

theorem rbF_eq {η : Nat} (hη : η = 2 ∨ η = 4) {b : Nat} (hb : b < rbBound η) :
    rbF η (BitVec.ofNat 32 b) = zw (ofInt (rbC η b)) := by
  rcases hη with rfl | rfl
  · exact rbF_eq2 b hb
  · exact rbF_eq4 b hb

theorem hbTry_eq {η : Nat} (hη : η = 2 ∨ η = 4) (L : List Zq) (b : Nat) :
    hbTry η L b = if b < rbBound η then L ++ [ofInt (rbC η b)] else L := by
  unfold hbTry
  rw [coeffFromHalfByte_eq hη]
  by_cases h : b < rbBound η <;> simp [h]

theorem halfByteOk_eq {η : Nat} (hη : η = 2 ∨ η = 4) (b : Nat) :
    halfByteOk η b = if b < rbBound η then 1 else 0 := by
  unfold halfByteOk
  rw [coeffFromHalfByte_eq hη]
  by_cases h : b < rbBound η <;> simp [h]

/-- Half-bytes accepted alike. -/
theorem bound_congr {η : Nat} (hη : η = 2 ∨ η = 4) {b₁ b₂ : Nat} (h : halfByteOk η b₁ = halfByteOk η b₂) :
    decide (rbBound η ≤ b₁) = decide (rbBound η ≤ b₂) := by
  rw [halfByteOk_eq hη, halfByteOk_eq hη] at h
  by_cases h₁ : b₁ < rbBound η <;> by_cases h₂ : b₂ < rbBound η <;> simp [h₁, h₂] at h ⊢ <;> omega

theorem rbBound_le {η : Nat} (hη : η = 2 ∨ η = 4) : rbBound η ≤ 15 := by
  rcases hη with rfl | rfl <;> decide

theorem rbBound_enc {η : Nat} (hη : η = 2 ∨ η = 4) : encodable (BitVec.ofNat 32 (rbBound η)) = true := by
  rcases hη with rfl | rfl <;> decide

/-- `rbVal η`: the coefficient in `r10`, through `r9` and `r11`. -/
theorem rbVal_ok {η : Nat} (hη : η = 2 ∨ η = 4) (s : State) :
    WP isa (.block (rbVal η)) s fun s' => s'.gpr .r10 = rbF η (s.gpr .r9) ∧
      (∀ r, r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
        s'.wr = s.wr ∧ s'.sp = s.sp := by
  rcases hη with rfl | rfl
  · simp only [rbVal, csub, Impl.MlDsa.Arm.Pack.addQNeg]
    run_block [and_true]
    exact ⟨rfl, fun r h9 h10 h11 => by simp [h9, h10, h11]⟩
  · simp only [rbVal, Impl.MlDsa.Arm.Pack.addQNeg]
    run_block [and_true]
    exact ⟨rfl, fun r _ h10 h11 => by simp [h10, h11]⟩

/-! ## The invariant between the pieces -/

/-- Iteration `t`, with the coefficients `L` stored, for the XOF output `X`. -/
structure Base (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) 544 = X
  r0 : s.gpr .r0 = P.scr + BitVec.ofNat 32 (840 + t)
  r3 : s.gpr .r3 = BitVec.ofNat 32 (544 - t)
  r2 : s.gpr .r2 = BitVec.ofNat 32 L.length
  len : L.length ≤ 256
  st : Stored s.mem P.A L

/-- `Base` after code that changes no memory and none of `r0`, `r2`, `r3`,
`r5` and `r6`. -/
theorem Base.regs {P : Sp} {σ : State} {X : List Byte} {t : Nat} {L : List Zq} {s s' : State}
    (h : Base P σ X t L s) (hg : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → r ≠ .r11 → s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : Base P σ X t L s' :=
  ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, hsp.trans h.env.sp,
      (hg .r5 (by decide) (by decide) (by decide) (by decide)).trans h.env.r5,
      (hg .r6 (by decide) (by decide) (by decide) (by decide)).trans h.env.r6,
      by rw [hm]; exact h.env.sav, by rw [hm]; exact h.env.savlr, by rw [hm]; exact h.env.frame⟩,
    by rw [hm]; exact h.out, (hg .r0 (by decide) (by decide) (by decide) (by decide)).trans h.r0,
    (hg .r3 (by decide) (by decide) (by decide) (by decide)).trans h.r3,
    (hg .r2 (by decide) (by decide) (by decide) (by decide)).trans h.r2, h.len, by rw [hm]; exact h.st⟩

/-! ## A try -/

/-- After the test of a try: `Z` is whether the half-byte `b` is rejected. -/
structure TS (η : Nat) (P : Sp) (σ : State) (X : List Byte) (t : Nat) (L : List Zq) (b : Nat) (v : BitVec 32)
    (s : State) : Prop where
  base : Base P σ X t L s
  r9 : s.gpr .r9 = BitVec.ofNat 32 b
  r8 : s.gpr .r8 = v
  z : s.z = decide (rbBound η ≤ b)

/-- The test of a try. -/
theorem tsgn_ok {η : Nat} (hη : η = 2 ∨ η = 4) {P : Sp} {σ : State} {X : List Byte} {t : Nat} {L : List Zq}
    {b : Nat} (hb : b < 16) {v : BitVec 32} {s : State} (h : Base P σ X t L s) (h9 : s.gpr .r9 = BitVec.ofNat 32 b)
    (h8 : s.gpr .r8 = v) :
    WP isa (.block [.dp .sub .r11 .r9 (.imm (BitVec.ofNat 32 (rbBound η))), .mov .r11 (.shifted .r11 .lsr 31),
      .cmp .r11 (.imm 0)]) s (TS η P σ X t L b v) := by
  have e9 : (s.gpr .r9).toNat = b := by rw [h9, toNat_ofNat32 (by omega)]
  have hB := rbBound_le hη
  refine WP.mono (sgn_ok s .r9 (.imm (BitVec.ofNat 32 (rbBound η))) (y := BitVec.ofNat 32 (rbBound η))
    (by simp only [Op2.eval, rbBound_enc hη, ite_true]) (by omega) (by rw [toNat_ofNat32 (by omega)]; omega))
    fun s' ⟨hz, hg, hm, hrd, hwr, hsp⟩ => ⟨h.regs (fun r _ _ _ h11 => hg r h11) hm hrd hwr hsp,
      by rw [hg .r9 (by decide), h9], by rw [hg .r8 (by decide), h8], by rw [hz, e9, toNat_ofNat32 (by omega)]⟩

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

/-- The XOF output is apart from the output polynomial. -/
theorem out_disj : (⟨P.at' 840, 544⟩ : Region).Disjoint P.aR :=
  (hp.a_scr.sub_right (sub_scr (a := 840) (n := 544) (by omega))).symm

/-- An accepted half-byte: its coefficient stored. -/
theorem acc_ok {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat} {L : List Zq} {b : Nat} {v : BitVec 32}
    {s : State} (h : TS η P σ X t L b v s) (hL : L.length < 256) (hb : b < rbBound η) :
    WP isa (.block (rbVal η ++ storeJ .r10)) s fun s' =>
      Base P σ X t (L ++ [ofInt (rbC η b)]) s' ∧ s'.gpr .r8 = v := by
  rw [WP.block_append_iff]
  refine WP.mono (rbVal_ok hη s) fun s1 ⟨h10, hg, hm, hrd, hwr, hsp⟩ => ?_
  have b1 : Base P σ X t L s1 := h.base.regs (fun r _ h9 h10 h11 => hg r h9 h10 h11) hm hrd hwr hsp
  refine WP.mono (storeJ_stored hp b1.env (v := .r10) (by decide) b1.r2 hL b1.st (x := ofInt (rbC η b))
    (by rw [h10, h.r9, rbF_eq hη hb])) fun s2 ⟨hst, h2, hg2, _, he2, hf⟩ => ⟨⟨he2, ?_, ?_, ?_, h2, ?_, hst⟩, ?_⟩
  · rw [MlKem.bytesAt_frame hf (fun r hr => by
      rw [List.mem_singleton] at hr; subst hr; exact out_disj hp) (by omega)]
    exact b1.out
  · rw [hg2 .r0 (by decide) (by decide)]; exact b1.r0
  · rw [hg2 .r3 (by decide) (by decide)]; exact b1.r3
  · rw [List.length_append, List.length_singleton]; omega
  · rw [hg2 .r8 (by decide) (by decide), hg .r8 (by decide) (by decide) (by decide)]; exact h.r8

end

/-- A try: the half-byte `b` in `r9` tried, with `r8` kept. -/
theorem try_ok {P : Sp} {σ : State} (hp : SpOk P σ) {η : Nat} (hη : η = 2 ∨ η = 4) {X : List Byte} {t : Nat}
    {L : List Zq} {b : Nat} (hb : b < 16) {s : State} (h : Base P σ X t L s) (hL : L.length < 256)
    (h9 : s.gpr .r9 = BitVec.ofNat 32 b) :
    WP isa (rbTry η) s fun s' => Base P σ X t (hbTry η L b) s' ∧ s'.gpr .r8 = s.gpr .r8 := by
  refine WP.seq (WP.mono (tsgn_ok hη hb h h9 rfl) fun s1 h1 => ?_)
  rw [hbTry_eq hη]
  refine WP.ite (decide (rbBound η ≤ b)) (by show some s1.z = _; rw [h1.z]) (fun hr => ?_) (fun hr => ?_)
  · simp only [decide_eq_true_eq] at hr
    rw [ifF (by omega)]
    exact WP.block_nil ⟨h1.base, h1.r8⟩
  · simp only [decide_eq_false_iff_not] at hr
    rw [ifT (by omega)]
    exact acc_ok hp hη h1 hL (by omega)

end VG.Proof.MlDsa.Arm.Sample.RejBounded
