import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejBoundedCT
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_bounded_poly`, constant time and `Verified`

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the public data (the pointers, `η`, the stack pointer, and which
half-bytes of the XOF output are accepted, `rejBoundedLeak`) leak the same
trace: the prologue and the blocks around the loop by the taint analysis,
the sponge by `sponge_ct`, the branch on `η` because `η` is public, and the
loop iteration by iteration (`loop_ct`), since the half-bytes of the first
544 bytes of output are accepted alike (`leak_hbOks`).
-/

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample (hbOks leak_hbOks rejBounded_some rejBounded_none stored_polyIs H_length)
open VG.Spec.MlDsa (H rejBoundedContract rejBoundedSig rejBoundedLeak)
open VG.Spec.Sha3 (bytesAt)
open RejBounded

namespace RejBounded

/-- The test of `η = 2`. -/
theorem cmp_ok {P : Sp} {σ s : State} (h : J6 136 544 P σ s) :
    WP isa (.block [.cmp .r7 (.imm 2)]) s fun s' => J6 136 544 P σ s' ∧ s'.z = decide (P.prm.toNat = 2) := by
  have e7 := h.r7
  refine WP.mono (Q := fun s1 => s1 = subFlags s P.prm 2) (by run_block [e7]) fun s1 e1 => ?_
  subst e1
  refine ⟨⟨⟨h.env.rd, h.env.wr, h.env.sp, h.env.r5, h.env.r6, h.env.sav, h.env.savlr, h.env.frame⟩, h.r7, h.out⟩,
    ?_⟩
  show (P.prm - BitVec.ofNat 32 2 == 0) = _
  rw [cmp_z _ _ (by decide)]

section
variable {P : Sp} {σ₁ σ₂ : State} (hp₁ : SpOk P σ₁) (hp₂ : SpOk P σ₂)
include hp₁ hp₂

/-- The loop for `η`, from the sponge's output. -/
theorem rbLoop_ct {η : Nat} (hη : η = 2 ∨ η = 4)
    (oks : (H (P.msg σ₁) 544).map (hbOks η) = (H (P.msg σ₂) 544).map (hbOks η)) {h1 h2 h3 : VG.Taint.Hint VG.Arm.taint.T}
    (c1 : (VG.Arm.taint.check (Taint.ofRegs []) (.block (tsgn η)) h1).isSome = true)
    (c2 : (VG.Arm.taint.check (Taint.ofRegs [.r2, .r5]) (.block (rbVal η ++ storeJ .r10)) h2).isSome = true)
    (c3 : (VG.Arm.taint.check (Taint.ofRegs []) (.block []) h3).isSome = true) :
    RelCT isa (fun a b => J6 136 544 P σ₁ a ∧ J6 136 544 P σ₂ b) (rbLoop η) fun a b =>
      Base P σ₁ (H (P.msg σ₁) 544) 544 (Lf η (H (P.msg σ₁) 544) 544) a ∧
        Base P σ₂ (H (P.msg σ₂) 544) 544 (Lf η (H (P.msg σ₂) 544) 544) b :=
  RelCT.seq (relW (taintRel [.r6] (fun a b h r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6]) (by taint_decide))
      fun a b h => ⟨init_ok h.1, init_ok h.2⟩)
    (loop_ct hp₁ hp₂ hη c1 c2 c3 (H_length _ _) (H_length _ _) oks)

/-- The branch on `η`, and the loops. -/
theorem sel_ct (hη : P.prm.toNat = 2 ∨ P.prm.toNat = 4)
    (oks : (H (P.msg σ₁) 544).map (hbOks P.prm.toNat) = (H (P.msg σ₂) 544).map (hbOks P.prm.toNat)) :
    RelCT isa (fun a b => J6 136 544 P σ₁ a ∧ J6 136 544 P σ₂ b)
      (.seq (.block [.cmp .r7 (.imm 2)]) (.ite .eq (rbLoop 2) (rbLoop 4))) fun a b =>
      Base P σ₁ (H (P.msg σ₁) 544) 544 (Lf P.prm.toNat (H (P.msg σ₁) 544) 544) a ∧
        Base P σ₂ (H (P.msg σ₂) 544) 544 (Lf P.prm.toNat (H (P.msg σ₂) 544) 544) b := by
  refine RelCT.seq (relW (taintRel [] nil_regs (by taint_decide)) fun a b h => ⟨cmp_ok h.1, cmp_ok h.2⟩) ?_
  rcases hη with e | e
  · rw [e] at oks ⊢
    refine RelCT.ite (fun a b h => by rw [eval_eq, eval_eq, h.1.2, h.2.2]) (RelCT.mono (rbLoop_ct hp₁ hp₂ (η := 2) (.inl rfl) oks (by taint_decide) (by taint_decide)
      (by taint_decide)) (fun a b h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h) (RelCT.of_false fun a b ⟨h, he⟩ => by
        rw [eval_eq, h.1.2] at he; exact absurd he (by decide))
  · rw [e] at oks ⊢
    refine RelCT.ite (fun a b h => by rw [eval_eq, eval_eq, h.1.2, h.2.2]) (RelCT.of_false fun a b ⟨h, he⟩ => by
        rw [eval_eq, h.1.2] at he; exact absurd he (by decide))
      (RelCT.mono (rbLoop_ct hp₁ hp₂ (η := 4) (.inr rfl) oks (by taint_decide) (by taint_decide)
        (by taint_decide)) (fun a b h => ⟨h.1.1.1, h.1.2.1⟩) fun _ _ h => h)

end

/-- The precondition, as `SpOk` and `η`. -/
theorem pre_of {s : State} (h : (rejBoundedContract Arm.abi 8).pre s) :
    SpOk (spOf s) s ∧ (etaOf s = 2 ∨ etaOf s = 4) := by
  sig_pre [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f0, f2, f3, he⟩ := h
  exact ⟨⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f0, show (66 : Nat) < 2 ^ 32 by decide, f2, f3, h8⟩, he⟩

section
variable {σ₁ σ₂ : State} (hp₁ : SpOk (spOf σ₁) σ₁) (hp₂ : SpOk (spOf σ₂) σ₂) (hη : etaOf σ₁ = 2 ∨ etaOf σ₁ = 4)
  (hsp : σ₁.sp = σ₂.sp) (h0 : σ₁.gpr .r0 = σ₂.gpr .r0) (h1 : σ₁.gpr .r1 = σ₂.gpr .r1)
  (h2 : σ₁.gpr .r2 = σ₂.gpr .r2) (h3 : σ₁.gpr .r3 = σ₂.gpr .r3)
  (hl : rejBoundedLeak (etaOf σ₁) ((spOf σ₁).msg σ₁) = rejBoundedLeak (etaOf σ₂) ((spOf σ₂).msg σ₂))
include hp₁ hp₂ hη hsp h0 h1 h2 h3 hl

/-- The whole function, from two entry states that agree on the public data. -/
theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) rejBounded fun _ _ => True := by
  have eP : spOf σ₂ = spOf σ₁ := by simp only [spOf, h0, h1, h2, h3]
  rw [eP] at hp₂ hl
  have e1 : etaOf σ₂ = etaOf σ₁ := by rw [etaOf, etaOf, h1]
  rw [e1] at hl
  have oks := leak_hbOks hl (B := 544) (by decide)
  refine RelCT.seq (relW (taintRel [.r0, .r1, .r2, .r3] (fun a b h r hr => ?_) (by taint_decide)) fun a b h =>
    ⟨by rw [h.1]; exact pro_ok hp₁, by rw [h.2]; exact pro_rb hp₂ h0.symm h1.symm h2.symm h3.symm rfl⟩) ?_
  · rw [h.1, h.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  refine RelCT.seq (sponge_ct hp₁ hp₂ hsp (rate := 136) (outlen := 544) (by decide) (by decide) (by decide)
    (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (sel_ct hp₁ hp₂ hη oks) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6]) (by taint_decide)

end

end RejBounded

end VG.Proof.MlDsa.Arm.Sample

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm (setWidth_append32)
open VG.Proof.MlDsa.Sample (rbFold rejBounded_some rejBounded_none stored_polyIs ifT ifF)
open VG.Spec.MlDsa (rejBoundedContract rejBoundedSig)
open RejBounded

/-- A state satisfying the precondition. -/
def rbSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 2 | .r2 => 0x2000 | .r3 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 66⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

theorem rejBounded_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.rejBounded (rejBoundedContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ⟨rbSat, ?_⟩⟩
  · obtain ⟨hp, hη⟩ := pre_of hs
    obtain ⟨t, s', he, ha, h0, hst⟩ := correct hp hη
    refine ⟨t, s', he, ha, ?_⟩
    have hL : Lf (etaOf s) (X s) 544 = rbFold (etaOf s) [] (X s) := by
      simp only [Lf]; rw [List.take_of_length_le (by rw [X_length])]
    rw [hL] at h0 hst
    sig_post [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [setWidth_append32, h0]
    by_cases hf : (rbFold (etaOf s) [] (X s)).length = 256
    · rw [ifT hf]
      obtain ⟨hred, hpoly⟩ := stored_polyIs hst hf
      exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejBounded := 544 }, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 544 _) = _
        exact (rejBounded_some _ hf).trans (congrArg some hpoly.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
        show Option.map _ (Spec.MlDsa.rejBoundedPoly _ 481 _) = none
        exact (congrArg (Option.map _) (rejBounded_none _ (B := 544) (by decide) hf)).trans rfl⟩⟩
  · obtain ⟨hp₁, hη⟩ := pre_of h₁
    obtain ⟨hp₂, -⟩ := pre_of h₂
    sig_pub [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2, h3⟩ := hpub
    exact (all_ct hp₁ hp₂ hη hsp h0 h1 h2 h3 hb s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · sig_apply_check
    · decide +kernel
    · sig_reduce [rejBoundedContract, rejBoundedSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      sig_and_intros
      all_goals first
        | trivial
        | decide +kernel

end VG.Proof.MlDsa.Arm.Sample
