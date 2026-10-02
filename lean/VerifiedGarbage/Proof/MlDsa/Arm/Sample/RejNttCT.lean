import VerifiedGarbage.Proof.MlDsa.Arm.Sample.RejNtt
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.MlDsa.Poly

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_rej_ntt_poly`, constant time but for the seed, and `Verified`

Two runs from entry states whose seeds (the declared leak), pointers and stack
pointers agree leak the same (`all_ct`): the prologue and the blocks around
the loop by the taint analysis, the sponge by `sponge_ct`, and the loop, whose
branches and stores depend on the XOF output, by relating the two runs
iteration by iteration (`body_ct`): both are at the same iteration with the
same coefficients sampled and the same bytes to read, so each branch goes the
same way and each store goes to the same address.
-/

namespace VG.Proof.MlDsa.Arm.Sample.RejNtt

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q G PolyIs)
open VG.Spec.Sha3 (bytesAt)

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  hp₁ : SpOk (spOf σ₁) σ₁
  hp₂ : SpOk (spOf σ₂) σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  B : B σ₁ = B σ₂

theorem nil_regs {R : State → State → Prop} : ∀ x y, R x y → ∀ r ∈ ([] : List Reg), x.gpr r = y.gpr r :=
  fun _ _ _ _ h => absurd h List.not_mem_nil

section
variable {σ₁ σ₂ : State} (h : Two σ₁ σ₂)
include h

theorem sp_eq : spOf σ₂ = spOf σ₁ := by simp only [spOf, h.r0, h.r1, h.r2]

theorem X_eq : X σ₁ = X σ₂ := by simp only [X, h.B]

theorem Lt_eq (t : Nat) : Lt σ₁ t = Lt σ₂ t := by simp only [Lt, X_eq h]

theorem V_eq (t : Nat) : V σ₁ t = V σ₂ t := by simp only [V, Xb, X_eq h]

/-! ## The loop -/

theorem try_ct {t : Nat} :
    RelCT isa (fun a b => (M1 σ₁ t a ∧ M1 σ₂ t b) ∧ isa.eval .eq a = some false) rnTry fun _ _ => True := by
  have hz : ∀ a b, (M1 σ₁ t a ∧ M1 σ₂ t b) ∧ isa.eval .eq a = some false → a.z = false ∧ b.z = false :=
    fun a b hab => by
      have e : a.z = false := Option.some.inj hab.2
      refine ⟨e, ?_⟩
      rw [← e, hab.1.1.z, hab.1.2.z, Lt_eq h]
  refine RelCT.seq (R := fun a b => T1 σ₁ t a ∧ T1 σ₂ t b) (relW (taintRel [] nil_regs (by taint_decide))
    fun a b hab => ⟨tryA hab.1.1 (hz a b hab).1, tryA hab.1.2 (hz a b hab).2⟩) ?_
  refine RelCT.ite (fun a b hab => by
    show some a.z = some b.z; rw [hab.1.z, hab.2.z, V_eq h]) (taintRel [] nil_regs (by taint_decide))
    (taintRel [.r2, .r5] (fun a b hab r hr => ?_) (by taint_decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · rw [hab.1.1.lat.r2, hab.1.2.lat.r2, Lt_eq h]
  · rw [hab.1.1.lat.env.r5, hab.1.2.lat.env.r5, sp_eq h]

theorem body_ct {t : Nat} (ht : t < 336) :
    RelCT isa (fun a b => LAt σ₁ t a ∧ LAt σ₂ t b) rnBody fun a b =>
      (LAt σ₁ (t + 1) a ∧ a.z = decide (t + 1 = 336)) ∧ (LAt σ₂ (t + 1) b ∧ b.z = decide (t + 1 = 336)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relW ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => M1 σ₁ t a ∧ M1 σ₂ t b) (relW (taintRel [.r0, .r2] (fun a b hab r hr => ?_)
    (by taint_decide)) fun a b hab => ⟨pieceA hp₁ ht hab.1, pieceA hp₂ ht hab.2⟩) ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.r0, hab.2.r0, h.r2]
    · rw [hab.1.r2, hab.2.r2, Lt_eq h]
  refine RelCT.seq (R := fun a b => M2 σ₁ t a ∧ M2 σ₂ t b) (relW ?_
    fun a b hab => ⟨pieceB hp₁ ht hab.1, pieceB hp₂ ht hab.2⟩) (taintRel [] nil_regs (by taint_decide))
  exact RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hab.1.z, hab.2.z, Lt_eq h])
    (taintRel [] nil_regs (by taint_decide)) (try_ct h)

theorem loop_ct :
    RelCT isa (fun a b => LAt σ₁ 0 a ∧ LAt σ₂ 0 b) (.loop rnBody .ne) fun a b =>
      LAt σ₁ 336 a ∧ LAt σ₂ 336 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rnBody) (c := .ne)
    (Q := fun a b => LAt σ₁ 336 a ∧ LAt σ₂ 336 b)
    (fun n a b => ∃ t, t < 336 ∧ n = 336 - t ∧ LAt σ₁ t a ∧ LAt σ₂ t b) (fun n => ?_) 336)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 336 ∧ n = 336 - t ∧ LAt σ₁ t a ∧ LAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 336
  · by_cases hn : n = 336 - t
    · refine RelCT.mono (P := fun a b => LAt σ₁ t a ∧ LAt σ₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 336 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 336 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨336 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.rejNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  have eP := sp_eq h
  have hp₂' : SpOk (spOf σ₁) σ₂ := eP ▸ hp₂
  refine RelCT.seq (R := fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₁) σ₂ b) (relW (taintRel [.r0, .r1, .r2]
    (fun a b hab r hr => ?_) (by taint_decide)) fun a b hab => ⟨?_, ?_⟩) ?_
  · rw [hab.1, hab.2]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [h.r0, h.r1, h.r2]
  · rw [hab.1]; exact pro_rn hp₁ rfl rfl rfl rfl rfl
  · rw [hab.2]; exact pro_rn hp₂' h.r0.symm h.r1.symm h.r2.symm rfl rfl
  refine RelCT.seq (sponge_ct hp₁ hp₂' h.sp (rate := 168) (outlen := 1008) (by decide) (by decide) (by decide)
    (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (R := fun a b => LAt σ₁ 336 a ∧ LAt σ₂ 336 b) (RelCT.seq (R := fun a b => LAt σ₁ 0 a ∧ LAt σ₂ 0 b)
    (relW (taintRel [] nil_regs (by taint_decide)) fun a b hab => ⟨lat0 hab.1, lat0 (eP ▸ hab.2)⟩) (loop_ct h)) ?_
  exact taintRel [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.env.r6, hab.2.env.r6, sp_eq h]) (by taint_decide)

end

/-! ## `Verified` -/

theorem spOk_of {s : State} (h : (Spec.MlDsa.rejNTTContract Arm.abi 8).pre s) : SpOk (spOf s) s := by
  sig_pre [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, b1, b2, b3, f0, f1, f2⟩ := h
  exact ⟨by rw [hrd]; exact List.mem_singleton_self _, hwr, d1, d2, d3, b1, b2, b3, f0,
    show (34 : Nat) < 2 ^ 32 by decide, f1, f2, h8⟩

theorem leakBytes_inj : ∀ {a b : List Byte}, a.map (fun x => x.toNat) = b.map (fun x => x.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, leakBytes_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r2 => 0x3000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := [⟨0x1000, 34⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.RejNtt

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Sample
open RejNtt

theorem rejNTT_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.rejNTT (Spec.MlDsa.rejNTTContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h0, hpoly, ha⟩ := correct (spOk_of hs)
    refine ⟨t, s', he, ha, ?_⟩
    sig_post [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val]
    rw [setWidth_append32, h0]
    by_cases hf : (rnFold [] (X s)).length = 256
    · rw [ifT hf]
      have hpi := hpoly hf
      exact ⟨fun _ => hpi.1, .inl ⟨rfl, { Spec.MlDsa.minBounds with rejNTT := 1008 }, by
        show Spec.MlDsa.rejNTTPoly 1008 _ = _
        exact (rejNTT_some hf).trans (congrArg some hpi.2.symm)⟩⟩
    · rw [ifF hf]
      exact ⟨fun e => absurd e (by decide), .inr ⟨rfl, rejNTT_none (B := 1008) (by decide) (by decide) hf⟩⟩
  · sig_pub [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2⟩ := hpub
    exact (all_ct ⟨spOk_of h₁, spOk_of h₂, hsp, h0, h1, h2, leakBytes_inj hb⟩ s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩
      e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlDsa.rejNTTContract, Spec.MlDsa.rejNTTSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample
