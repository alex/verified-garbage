import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedBody

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_bounded_poly`, correctness

The function runs in pieces: the prologue (`J0`), the sponge, whose output is
`H(ρ, 544)` (`J6`), the branch on `η`, and the loop for `η`, iteration `t` of
which starts from `Base` with the coefficients `rbFold` samples from the first
`t` bytes of output stored (`loop_ok`); then the end returns whether there are 256.
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejBounded

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (Stored stored_nil H_eq H_length)
open VG.Spec.MlDsa (Zq H)
open VG.Spec.Sha3 (bytesAt)

/-- `η`, the argument in `r1`. -/
abbrev etaOf (σ : State) : Nat := (σ.gpr .r1).toNat

/-- The call, from its entry state: `seed = r0`, `eta = r1`, `a = r2`,
`scratch = r3`. -/
abbrev spOf (σ : State) : Sp := ⟨σ.gpr .r0, 66, σ.gpr .r3, σ.gpr .r2, σ.gpr .r1⟩

/-- The XOF output the function uses: 544 bytes of `H(ρ)`. -/
abbrev X (σ : State) : List Byte := H ((spOf σ).msg σ) 544

theorem X_length (σ : State) : (X σ).length = 544 := H_length _ _

/-- The prologue. -/
theorem pro_ok {σ : State} (hp : SpOk (spOf σ) σ) :
    WP isa (.block (pro .r3 .r2 (.reg .r1) (.imm 66) .r0)) σ (J0 (spOf σ) σ) :=
  pro_rb hp rfl rfl rfl rfl rfl

section
variable {P : Sp} {σ : State}

/-- The loop's setup, from the sponge's output. -/
theorem init_ok {s : State} (h : J6 136 544 P σ s) :
    WP isa (.block [.dp .add .r0 .r6 (.imm 840), .mov .r2 (.imm 0), .mov .r3 (.imm 544)]) s
      (Base P σ (H (P.msg σ) 544) 0 []) := by
  have e6 := h.env.r6
  refine WP.mono (Q := fun s' : State => s'.gpr .r0 = P.scr + BitVec.ofNat 32 840 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
      s'.gpr .r3 = BitVec.ofNat 32 544 ∧ (∀ r, r ≠ .r0 → r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp) (by
    run_block [e6, and_true]
    exact ⟨rfl, trivial, trivial, fun r h0 h2 h3 => by simp [h0, h2, h3]⟩)
    fun s' ⟨h0, h2, h3, hg, hm, hrd, hwr, hsp⟩ => ⟨⟨hrd.trans h.env.rd, hwr.trans h.env.wr, hsp.trans h.env.sp,
      (hg .r5 (by decide) (by decide) (by decide)).trans h.env.r5,
      (hg .r6 (by decide) (by decide) (by decide)).trans h.env.r6,
      by rw [hm]; exact h.env.sav, by rw [hm]; exact h.env.savlr, by rw [hm]; exact h.env.frame⟩,
      by rw [hm, h.out, H_eq], h0, h3, h2, by simp, stored_nil _ _⟩

/-- The loop for `η`. -/
theorem loop_ok (hp : SpOk P σ) {η : Nat} (hη : η = 2 ∨ η = 4) {s : State} (h : J6 136 544 P σ s) :
    WP isa (rbLoop η) s (Base P σ (H (P.msg σ) 544) 544 (Lf η (H (P.msg σ) 544) 544)) :=
  WP.seq (WP.mono (init_ok h) fun _ h0 =>
    wp_loop_ne (fun t s => Base P σ (H (P.msg σ) 544) t (Lf η (H (P.msg σ) 544) t) s) (N := 544) (by decide)
      (fun _ ht _ hs => body_ok hp hη (H_length _ _) ht hs) (fun _ h => h) h0)

end

/-- The branch on `η`, and the loop for it. -/
theorem sel_ok {σ : State} (hp : SpOk (spOf σ) σ) (hη : etaOf σ = 2 ∨ etaOf σ = 4) {s : State}
    (h : J6 136 544 (spOf σ) σ s) :
    WP isa (.seq (.block [.cmp .r7 (.imm 2)]) (.ite .eq (rbLoop 2) (rbLoop 4))) s
      (Base (spOf σ) σ (X σ) 544 (Lf (etaOf σ) (X σ) 544)) := by
  have e7 := h.r7
  refine WP.seq (WP.mono (Q := fun s1 => s1 = subFlags s (σ.gpr .r1) 2) (by
    run_block [e7]) fun s1 e1 => ?_)
  subst e1
  have hj : J6 136 544 (spOf σ) σ (subFlags s (σ.gpr .r1) 2) :=
    ⟨⟨h.env.rd, h.env.wr, h.env.sp, h.env.r5, h.env.r6, h.env.sav, h.env.savlr, h.env.frame⟩, h.r7, h.out⟩
  have hz : isa.eval .eq (subFlags s (σ.gpr .r1) 2) = some (decide (etaOf σ = 2)) := by
    show some (σ.gpr .r1 - BitVec.ofNat 32 2 == 0) = _
    rw [cmp_z _ _ (by decide)]
  refine WP.ite _ hz (fun he => ?_) (fun he => ?_)
  · simp only [decide_eq_true_eq] at he
    rw [he]
    exact loop_ok hp (η := 2) (.inl rfl) hj
  · simp only [decide_eq_false_iff_not] at he
    have e4 : etaOf σ = 4 := hη.resolve_left he
    rw [e4]
    exact loop_ok hp (η := 4) (.inr rfl) hj

/-- The whole function: the calling convention, `r0` whether the loop
sampled 256 coefficients, and those stored. -/
theorem correct {σ : State} (hp : SpOk (spOf σ) σ) (hη : etaOf σ = 2 ∨ etaOf σ = 4) :
    WP isa rejBounded σ fun s' => abiPreserved σ s' ∧
      s'.gpr .r0 = (if (Lf (etaOf σ) (X σ) 544).length = 256 then 1 else 0) ∧
      Stored s'.mem (spOf σ).A (Lf (etaOf σ) (X σ) 544) :=
  WP.seq (WP.mono (pro_ok hp) fun _ h1 =>
    WP.seq (WP.mono (sponge_ok hp (rate := 136) (outlen := 544) (by decide) (by decide) (by decide) (by decide) h1)
      fun _ h2 => WP.seq (WP.mono (sel_ok hp hη h2) fun _ h3 =>
        WP.mono (retEpi_ok hp h3.env h3.r2 h3.len) fun _ ⟨h0, hm, ha⟩ => ⟨ha, h0, by rw [hm]; exact h3.st⟩)))

end VG.Proof.MlDsa.Arm.Sample.RejBounded
