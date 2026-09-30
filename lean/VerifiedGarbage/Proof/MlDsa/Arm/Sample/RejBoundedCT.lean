import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedRun

/-!
# ML-DSA on 32-bit ARM: the loop of `vg_mldsa_rej_bounded_poly`, constant time

Untrusted: everything here is checked by Lean. Two runs of the loop for
`η`, whose XOF outputs `X₁` and `X₂` have their half-bytes accepted alike
(`hbOks`, which the leak of the contract determines), leak the same: at
iteration `t`, both runs have sampled as many coefficients
(`rbFold_length_congr`), so the tests of `j ≥ 256` agree, and the byte to
read has its half-bytes accepted alike, so the tests of the tries agree;
the coefficients themselves are computed and stored by code that the taint
analysis proves leaks nothing of them but `j` and the output pointer
(`try_ct`). What each run is at each point comes from the correctness
proof (`relW`).
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbTry rbStep rbFold hbOks ifT ifF hbTry_length rbFold_length_congr)
open VG.Spec.MlDsa (Zq halfByteOk)

theorem nil_regs {R : State → State → Prop} : ∀ x y, R x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ hr => absurd hr List.not_mem_nil

/-- The first block of a try, as the taint analysis sees it. -/
abbrev tsgn (η : Nat) : List Instr :=
  [.dp .sub .r11 .r9 (.imm (BitVec.ofNat 32 (rbBound η))), .mov .r11 (.shifted .r11 .lsr 31), .cmp .r11 (.imm 0)]

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂) {η : Nat} (hη : η = 2 ∨ η = 4)
  {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
  (c1 : (VG.Arm.taint.check (Taint.ofRegs []) (.block (tsgn η)) h1).isSome = true)
  (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r2, .r5]) (.block (rbVal η ++ storeJ .r10)) h2).isSome = true)
  (c3 : (VG.Arm.taint.check (Taint.ofRegs []) (.block []) h3).isSome = true)
  {X₁ X₂ : List Byte}

/-- The eval of `.eq` is the flag `Z`. -/
theorem eval_eq (s : State) : isa.eval .eq s = some s.z := rfl

include hp₁ hp₂ hη c1 c2 c3 in
/-- A try, in two runs with as many coefficients and half-bytes accepted
alike. -/
theorem try_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length) (hL : L₁.length < 256) {b₁ b₂ : Nat}
    (hb₁ : b₁ < 16) (hb₂ : b₂ < 16) (hok : halfByteOk η b₁ = halfByteOk η b₂) {v₁ v₂ : BitVec 32} :
    RelCT isa (fun a c => (Base P σ₁ X₁ t L₁ a ∧ a.gpr .r9 = BitVec.ofNat 32 b₁ ∧ a.gpr .r8 = v₁) ∧
        (Base P σ₂ X₂ t L₂ c ∧ c.gpr .r9 = BitVec.ofNat 32 b₂ ∧ c.gpr .r8 = v₂)) (rbTry η)
      fun a c => (Base P σ₁ X₁ t (hbTry η L₁ b₁) a ∧ a.gpr .r8 = v₁) ∧
        (Base P σ₂ X₂ t (hbTry η L₂ b₂) c ∧ c.gpr .r8 = v₂) := by
  have hbc := bound_congr hη hok
  refine RelCT.seq (R := fun a c => TS η P σ₁ X₁ t L₁ b₁ v₁ a ∧ TS η P σ₂ X₂ t L₂ b₂ v₂ c)
    (relW (taintRel [] nil_regs c1) fun a c h =>
      ⟨tsgn_ok hη hb₁ h.1.1 h.1.2.1 h.1.2.2, tsgn_ok hη hb₂ h.2.1 h.2.2.1 h.2.2.2⟩) ?_
  refine RelCT.ite (fun a c h => by rw [eval_eq, eval_eq, h.1.z, h.2.z, hbc]) ?_ ?_
  · refine relW (taintRel [] nil_regs c3) fun a c ⟨⟨t₁, t₂⟩, he⟩ => ?_
    have r₁ : rbBound η ≤ b₁ := by
      rw [eval_eq, t₁.z] at he; simpa using he
    have r₂ : rbBound η ≤ b₂ := by
      rw [eval_eq, t₁.z, hbc] at he; simpa using he
    rw [hbTry_eq hη, hbTry_eq hη, ifF (by omega), ifF (by omega)]
    exact ⟨WP.block_nil ⟨t₁.base, t₁.r8⟩, WP.block_nil ⟨t₂.base, t₂.r8⟩⟩
  · refine relW (taintRel [.r2, .r5] (fun a c h r hr => ?_) c2) fun a c ⟨⟨t₁, t₂⟩, he⟩ => ?_
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.1.base.r2, h.1.2.base.r2, hl]
      · rw [h.1.1.base.env.r5, h.1.2.base.env.r5]
    have r₁ : b₁ < rbBound η := by
      rw [eval_eq, t₁.z] at he; simpa using he
    have r₂ : b₂ < rbBound η := by
      rw [eval_eq, t₁.z, hbc] at he; simpa using he
    rw [hbTry_eq hη, hbTry_eq hη, ifT r₁, ifT r₂]
    exact ⟨acc_ok hp₁ hη t₁ hL r₁, acc_ok hp₂ hη t₂ (by omega) r₂⟩

include hp₁ hp₂ hη c1 c2 c3 in
/-- The tries of an iteration, in two runs with as many coefficients and a
byte whose half-bytes are accepted alike. -/
theorem mid_ct {t : Nat} {L₁ L₂ : List Zq} (hl : L₁.length = L₂.length)
    (hok : hbOks η (zAt X₁ t) = hbOks η (zAt X₂ t)) :
    RelCT isa (fun a c => LD P σ₁ X₁ t L₁ a ∧ LD P σ₂ X₂ t L₂ c)
      (.ite .eq (.block []) (.seq (rbTry η) (.seq (.block rbHi) (.ite .eq (.block []) (rbTry η)))))
      fun a c => Base P σ₁ X₁ t (rbStep η L₁ (zAt X₁ t)) a ∧ Base P σ₂ X₂ t (rbStep η L₂ (zAt X₂ t)) c := by
  simp only [hbOks, Prod.mk.injEq] at hok
  rw [rbStep_eq, rbStep_eq]
  have hz : ∀ a c, (LD P σ₁ X₁ t L₁ a ∧ LD P σ₂ X₂ t L₂ c) → isa.eval .eq a = isa.eval .eq c := fun a c h => by
    rw [eval_eq, eval_eq, h.1.z, h.2.z, hl]
  by_cases hf : L₁.length < 256
  · rw [ifT hf, ifT (show L₂.length < 256 by omega)]
    refine RelCT.ite hz (RelCT.of_false fun a c ⟨h, he⟩ => by
      rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_true_eq] at he; omega) ?_
    have hm : (hbTry η L₁ ((zAt X₁ t).toNat % 16)).length = (hbTry η L₂ ((zAt X₂ t).toNat % 16)).length := by
      rw [hbTry_length, hbTry_length, hl, hok.1]
    refine RelCT.seq (R := fun (a c : State) =>
        (Base P σ₁ X₁ t (hbTry η L₁ ((zAt X₁ t).toNat % 16)) a ∧ a.gpr .r8 = BitVec.setWidth 32 (zAt X₁ t)) ∧
        (Base P σ₂ X₂ t (hbTry η L₂ ((zAt X₂ t).toNat % 16)) c ∧ c.gpr .r8 = BitVec.setWidth 32 (zAt X₂ t)))
      (RelCT.mono (try_ct hp₁ hp₂ hη c1 c2 c3 hl hf (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hok.1)
        (fun a c ⟨h, _⟩ => ⟨⟨h.1.base, h.1.r9, h.1.r8⟩, ⟨h.2.base, h.2.r9, h.2.r8⟩⟩) fun _ _ h => h) ?_
    refine RelCT.seq (R := fun (a c : State) => HI P σ₁ X₁ t (hbTry η L₁ ((zAt X₁ t).toNat % 16)) a ∧
        HI P σ₂ X₂ t (hbTry η L₂ ((zAt X₂ t).toNat % 16)) c)
      (relW (taintRel [] nil_regs (by taint_decide)) fun a c h => ⟨hi_ok h.1.1 h.1.2, hi_ok h.2.1 h.2.2⟩) ?_
    have hz2 : ∀ a c, (HI P σ₁ X₁ t (hbTry η L₁ ((zAt X₁ t).toNat % 16)) a ∧
        HI P σ₂ X₂ t (hbTry η L₂ ((zAt X₂ t).toNat % 16)) c) → isa.eval .eq a = isa.eval .eq c := fun a c h => by
      rw [eval_eq, eval_eq, h.1.z, h.2.z, hm]
    by_cases hm1 : (hbTry η L₁ ((zAt X₁ t).toNat % 16)).length < 256
    · rw [ifT hm1, ifT (show (hbTry η L₂ ((zAt X₂ t).toNat % 16)).length < 256 by omega)]
      refine RelCT.ite hz2 (RelCT.of_false fun a c ⟨h, he⟩ => by
        rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_true_eq] at he; omega) ?_
      refine RelCT.mono (try_ct hp₁ hp₂ hη c1 c2 c3 hm hm1 (b₁ := (zAt X₁ t).toNat / 16)
        (b₂ := (zAt X₂ t).toNat / 16) (by have := (zAt X₁ t).isLt; omega) (by have := (zAt X₂ t).isLt; omega)
        hok.2) (fun a c ⟨h, _⟩ => ⟨⟨h.1.base, h.1.r9, h.1.r8⟩, ⟨h.2.base, h.2.r9, h.2.r8⟩⟩)
        fun _ _ h => ⟨h.1.1, h.2.1⟩
    · rw [ifF hm1, ifF (show ¬ (hbTry η L₂ ((zAt X₂ t).toNat % 16)).length < 256 by omega)]
      refine RelCT.ite hz2 ?_ (RelCT.of_false fun a c ⟨h, he⟩ => by
        rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_false_iff_not] at he; omega)
      exact relW (taintRel [] nil_regs c3) fun a c h => ⟨WP.block_nil h.1.1.base, WP.block_nil h.1.2.base⟩
  · rw [ifF hf, ifF (show ¬ L₂.length < 256 by omega)]
    refine RelCT.ite hz ?_ (RelCT.of_false fun a c ⟨h, he⟩ => by
      rw [eval_eq, h.1.z] at he; simp only [Option.some.injEq, decide_eq_false_iff_not] at he; omega)
    exact relW (taintRel [] nil_regs c3) fun a c h => ⟨WP.block_nil h.1.1.base, WP.block_nil h.1.2.base⟩

variable (hX₁ : X₁.length = 544) (hX₂ : X₂.length = 544)
  (oks : X₁.map (hbOks η) = X₂.map (hbOks η))

include oks in
theorem len_eq (t : Nat) : (Lf η X₁ t).length = (Lf η X₂ t).length :=
  rbFold_length_congr rfl (by rw [List.map_take, List.map_take, oks])

include hX₁ hX₂ oks in
theorem ok_eq {t : Nat} (ht : t < 544) : hbOks η (zAt X₁ t) = hbOks η (zAt X₂ t) := by
  have h := congrArg (fun L => L[t]?) oks
  simp only [List.getElem?_map, List.getElem?_eq_getElem (show t < X₁.length by omega),
    List.getElem?_eq_getElem (show t < X₂.length by omega), Option.map_some, Option.some.injEq] at h
  rw [zAt, zAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (show t < X₁.length by omega), List.getElem?_eq_getElem (show t < X₂.length by omega)]
  exact h

include hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks in
/-- An iteration. -/
theorem body_ct {t : Nat} (ht : t < 544) :
    RelCT isa (fun a c => Base P σ₁ X₁ t (Lf η X₁ t) a ∧ Base P σ₂ X₂ t (Lf η X₂ t) c) (rbBody η)
      fun a c => (Base P σ₁ X₁ (t + 1) (Lf η X₁ (t + 1)) a ∧ a.z = decide (t + 1 = 544)) ∧
        (Base P σ₂ X₂ (t + 1) (Lf η X₂ (t + 1)) c ∧ c.z = decide (t + 1 = 544)) := by
  rw [Lf_succ η hX₁ ht, Lf_succ η hX₂ ht]
  refine RelCT.seq (R := fun a c => LD P σ₁ X₁ t (Lf η X₁ t) a ∧ LD P σ₂ X₂ t (Lf η X₂ t) c)
    (relW (taintRel [.r0] (fun a c h r hr => ?_) (by taint_decide)) fun a c h =>
      ⟨load_ok hp₁ ht h.1, load_ok hp₂ ht h.2⟩) ?_
  · rw [List.mem_singleton] at hr; subst hr; rw [h.1.r0, h.2.r0]
  refine RelCT.seq (mid_ct hp₁ hp₂ hη c1 c2 c3 (len_eq oks t) (ok_eq hX₁ hX₂ oks ht)) ?_
  exact relW (taintRel [] nil_regs (by taint_decide)) fun a c h => ⟨stepB_ok ht h.1, stepB_ok ht h.2⟩

include hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks in
/-- The loop. -/
theorem loop_ct :
    RelCT isa (fun a c => Base P σ₁ X₁ 0 (Lf η X₁ 0) a ∧ Base P σ₂ X₂ 0 (Lf η X₂ 0) c) (.loop (rbBody η) .ne)
      fun a c => Base P σ₁ X₁ 544 (Lf η X₁ 544) a ∧ Base P σ₂ X₂ 544 (Lf η X₂ 544) c := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rbBody η) (c := .ne)
    (Q := fun a c => Base P σ₁ X₁ 544 (Lf η X₁ 544) a ∧ Base P σ₂ X₂ 544 (Lf η X₂ 544) c)
    (fun n a c => ∃ t, t < 544 ∧ n = 544 - t ∧ Base P σ₁ X₁ t (Lf η X₁ t) a ∧ Base P σ₂ X₂ t (Lf η X₂ t) c)
    (fun n => ?_) 544) (fun a c hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.exists_ fun t => ?_
  by_cases ht : t < 544
  · by_cases hn : n = 544 - t
    · refine RelCT.mono (P := fun a c => Base P σ₁ X₁ t (Lf η X₁ t) a ∧ Base P σ₂ X₂ t (Lf η X₂ t) c)
        (body_ct hp₁ hp₂ hη c1 c2 c3 hX₁ hX₂ oks ht) (fun _ _ hab => hab.2.2)
        fun a c ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!c.z); rw [z₁, z₂]
      · have : t + 1 = 544 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 544 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨544 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

end

end VG.Proof.MlDsa.Arm.Sample.RejBounded
