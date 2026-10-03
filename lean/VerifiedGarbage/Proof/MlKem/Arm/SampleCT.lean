import VerifiedGarbage.Proof.MlKem.Arm.Sample

/-!
# ML-KEM on 32-bit ARM: `vg_mlkem_sample_ntt`, constant time and `Verified`

Two runs from states that agree on the public data (the pointers, the stack
pointer and the seed, which the contract lets the function leak) leak the same
trace (`RelCT`), phase by phase: the blocks by the taint analysis, from
registers that hold pointers in both runs (`taint_block`); the calls of the
sponge functions by `absorb_ct`, …, from their arguments, which are the same
in both runs; and the loop of Algorithm 7 iteration by iteration, whose
branches are on the same values in both runs because the XOF output is the
same, being that of the same seed (`body_ct`). What each run is at each point
comes from the correctness proof (`RelCT.wp`).
-/

namespace VG.Proof.MlKem.Arm.Sample

open VG VG.Arm VG.Impl.MlKem.Arm
open VG.Spec.MlKem
open VG.Spec.Sha3 (stateAt)

/-- Two runs, from states that agree on the public data. -/
structure Two (s₁ s₂ : State) : Prop where
  hp₁ : Pre s₁
  hp₂ : Pre s₂
  sp : s₁.sp = s₂.sp
  seed : pseed s₁ = pseed s₂
  a : pa s₁ = pa s₂
  scr : pscr s₁ = pscr s₂
  B : B s₁ = B s₂

theorem taint_block {P : State → State → Prop} {is : List Instr} (rs : List Reg)
    (hP : ∀ a b, P a b → ∀ r ∈ rs, a.gpr r = b.gpr r) {hc : VG.Taint.Hint VG.Arm.taint.T}
    (h : (VG.Arm.taint.check (Taint.ofRegs rs) (.block is) hc).isSome = true) :
    RelCT isa P (.block is) fun _ _ => True :=
  RelCT.taint (A := VG.Arm.taint) (Taint.ofRegs rs) (fun a b hab => Taint.agree_ofRegs (hP a b hab)) h

theorem relct_wp {c : Prog isa} {P : State → State → Prop} {F₁ F₂ : State → Prop}
    (hct : RelCT isa P c fun _ _ => True) (hw : ∀ a b, P a b → WP isa c a F₁ ∧ WP isa c b F₂) :
    RelCT isa P c fun a b => F₁ a ∧ F₂ b :=
  (hct.wp hw).mono (fun _ _ h => h) fun _ _ h => ⟨h.2.1, h.2.2⟩

section
variable {s₁ s₂ : State} (h : Two s₁ s₂)
include h

theorem Ls_eq (t : Nat) : Ls s₁ t = Ls s₂ t := by simp only [Ls, h.B]

theorem D1_eq (t : Nat) : D1 s₁ t = D1 s₂ t := by simp only [D1, h.B]

theorem D2_eq (t : Nat) : D2 s₁ t = D2 s₂ t := by simp only [D2, h.B]

/-! ## The loop -/

omit h in
/-- A candidate accepted or not, in both runs alike. -/
theorem accept_ct {d : Reg} (hd : d = .r10 ∨ d = .r11) {P : State → State → Prop} (hz : ∀ a b, P a b → a.z = b.z)
    (h1 : ∀ a b, P a b → a.gpr .r1 = b.gpr .r1) : RelCT isa P (accept d) fun _ _ => True := by
  refine RelCT.ite (fun a b hab => by show some a.z = some b.z; rw [hz a b hab]) ?_ ?_
  · exact taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
  · rcases hd with rfl | rfl
    · exact taint_block [.r1] (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact h1 a b hab.1) (by taint_decide)
    · exact taint_block [.r1] (fun a b hab r hr => by
        rw [List.mem_singleton] at hr; subst hr; exact h1 a b hab.1) (by taint_decide)

theorem body_ct {t : Nat} (ht : t < 280) :
    RelCT isa (fun a b => Inv s₁ t a ∧ Inv s₂ t b) rejBody fun a b =>
      (Inv s₁ (t + 1) a ∧ a.z = decide (t + 1 = 280)) ∧ (Inv s₂ (t + 1) b ∧ b.z = decide (t + 1 = 280)) := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine relct_wp ?_ fun a b hab => ⟨body_ok hp₁ ht hab.1, body_ok hp₂ ht hab.2⟩
  refine RelCT.seq (R := fun a b => P1 s₁ t a ∧ P1 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece1 hp₁ ht hab.1, piece1 hp₂ ht hab.2⟩) ?_
  · exact taint_block [.r0] (fun a b hab r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [hab.1.r0, hab.2.r0, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => P2 s₁ t a ∧ P2 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece2 hp₁ hab.1, piece2 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inl rfl) (fun a b hab => by rw [hab.1.z, hab.2.z, D1_eq h, Ls_eq h]) fun a b hab => ?_
    rw [hab.1.ls.r1, hab.2.ls.r1, h.a, Ls_eq h]
  refine RelCT.seq (R := fun a b => P3 s₁ t a ∧ P3 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece3 hab.1, piece3 hab.2⟩) ?_
  · exact taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)
  refine RelCT.seq (R := fun a b => P4 s₁ t a ∧ P4 s₂ t b) (relct_wp ?_ fun a b hab =>
    ⟨piece4 hp₁ hab.1, piece4 hp₂ hab.2⟩) ?_
  · refine accept_ct (.inr rfl) (fun a b hab => by rw [hab.1.z, hab.2.z, D1_eq h, D2_eq h, Ls_eq h])
      fun a b hab => ?_
    rw [hab.1.p2.ls.r1, hab.2.p2.ls.r1, h.a, Ls_eq h, D1_eq h]
  · exact taint_block [] (fun _ _ _ _ hr => absurd hr List.not_mem_nil) (by taint_decide)

theorem loop_ct :
    RelCT isa (fun a b => Inv s₁ 0 a ∧ Inv s₂ 0 b) (.loop rejBody .ne) fun a b =>
      Inv s₁ 280 a ∧ Inv s₂ 280 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := rejBody) (c := .ne)
    (Q := fun a b => Inv s₁ 280 a ∧ Inv s₂ 280 b)
    (fun n a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b) (fun n => ?_) 280)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 280 ∧ n = 280 - t ∧ Inv s₁ t a ∧ Inv s₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 280
  · by_cases hn : n = 280 - t
    · refine RelCT.mono (P := fun a b => Inv s₁ t a ∧ Inv s₂ t b) (body_ct h ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 280 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 280 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨280 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The sponge -/

theorem absorbPhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ stateAt a.mem (S s₁) = Spec.Sha3.zero) ∧
      (SEnv s₂ b ∧ stateAt b.mem (S s₂) = Spec.Sha3.zero)) (.seq (.block absorbSeedArgs) absorbCall)
      fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => SEnv s₀ s' ∧ s'.gpr .r0 = pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧ s'.gpr .r3 = pseed s₀ ∧
    s'.gpr .r12 = BitVec.ofNat 32 34 ∧ s'.gpr .lr = pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), SEnv s₀ s → WP isa (.block absorbSeedArgs) s (F s₀) := fun s₀ s hs =>
    WP.mono (absorbSeedArgs_ok hs.r4 hs.r6) fun _ ⟨hr, g0, g1, g2, g3, g12, glr⟩ =>
      ⟨hr.env hs, g0, g1, g2, g3, g12, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1, hw _ _ hab.2.1⟩) (absorb_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, a12, alr⟩, ⟨e₂, b0, b1, b2, b3, b12, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, _, absorb_args hp₁ e₁ a0 a1 a2 a3 a12 alr, by
      have := absorb_args hp₂ e₂ b0 b1 b2 b3 b12 blr
      rwa [← h.scr, ← h.seed] at this⟩)
  exact taint_block [.r4, .r6] (fun a b hab r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [hab.1.1.r4, hab.2.1.r4, h.seed]
    · rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

theorem padPhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ Spec.Sha3.Repr a.mem (S s₁) 168 (B s₁) ∧ (a.gpr .r0).toNat = 34) ∧
      (SEnv s₂ b ∧ Spec.Sha3.Repr b.mem (S s₂) 168 (B s₂) ∧ (b.gpr .r0).toNat = 34))
      (.seq (.block padArgs) padCall) fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => SEnv s₀ s' ∧ s'.gpr .r0 = pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 34 ∧ s'.gpr .r3 = BitVec.ofNat 32 0x1f ∧
    s'.gpr .lr = pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), SEnv s₀ s → (s.gpr .r0).toNat = 34 → WP isa (.block padArgs) s (F s₀) :=
    fun s₀ s hs h0 => WP.mono (padArgs_ok (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)) hs.r6)
      fun _ ⟨hr, g0, g1, g2, g3, glr⟩ => ⟨hr.env hs, g0, g1, g2, g3, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1 hab.1.2.2, hw _ _ hab.2.1 hab.2.2.2⟩) (pad_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, alr⟩, ⟨e₂, b0, b1, b2, b3, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, pad_args hp₁ e₁ a0 a1 a2 a3 alr, by
      have := pad_args hp₂ e₂ b0 b1 b2 b3 blr
      rwa [← h.scr] at this⟩)
  exact taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

theorem squeezePhase_ct :
    RelCT isa (fun a b => (SEnv s₁ a ∧ stateAt a.mem (S s₁) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₁)) ∧
      (SEnv s₂ b ∧ stateAt b.mem (S s₂) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₂)))
      (.seq (.block squeezeArgs) squeezeCall) fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  let F : State → State → Prop := fun s₀ s' => SEnv s₀ s' ∧ s'.gpr .r0 = pscr s₀ ∧
    s'.gpr .r1 = BitVec.ofNat 32 168 ∧ s'.gpr .r2 = BitVec.ofNat 32 0 ∧
    s'.gpr .r3 = pscr s₀ + BitVec.ofNat 32 840 ∧ s'.gpr .r12 = BitVec.ofNat 32 840 ∧
    s'.gpr .lr = pscr s₀ + BitVec.ofNat 32 200
  have hw : ∀ (s₀ s : State), SEnv s₀ s → WP isa (.block squeezeArgs) s (F s₀) := fun s₀ s hs =>
    WP.mono (squeezeArgs_ok hs.r6) fun _ ⟨hr, g0, g1, g2, g3, g12, glr⟩ => ⟨hr.env hs, g0, g1, g2, g3, g12, glr⟩
  refine RelCT.seq (R := fun a b => F s₁ a ∧ F s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨hw _ _ hab.1.1, hw _ _ hab.2.1⟩) (squeeze_ct fun a b ⟨⟨e₁, a0, a1, a2, a3, a12, alr⟩, ⟨e₂, b0, b1, b2, b3, b12, blr⟩⟩ =>
    ⟨by rw [e₁.sp, e₂.sp, h.sp], _, _, _, _, _, _, squeeze_args hp₁ e₁ a0 a1 a2 a3 a12 alr, by
      have := squeeze_args hp₂ e₂ b0 b1 b2 b3 b12 blr
      rwa [← h.scr] at this⟩)
  exact taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)

/-! ## The whole function -/

/-- What holds after each phase, in one run. -/
abbrev E1 (s₀ s : State) : Prop := SEnv s₀ s ∧ stateAt s.mem (S s₀) = Spec.Sha3.zero
abbrev E2 (s₀ s : State) : Prop := SEnv s₀ s ∧ Spec.Sha3.Repr s.mem (S s₀) 168 (B s₀) ∧ (s.gpr .r0).toNat = 34
abbrev E3 (s₀ s : State) : Prop :=
  SEnv s₀ s ∧ stateAt s.mem (S s₀) = VG.Proof.MlKem.padded 168 Spec.Sha3.shakeSuffix (B s₀)
abbrev E4 (s₀ s : State) : Prop :=
  SEnv s₀ s ∧ Spec.Sha3.bytesAt s.mem (S s₀ + BitVec.ofNat 64 840) 840 = xof (B s₀) 840

theorem all_ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) sampleNTT fun _ _ => True := by
  have hp₁ := h.hp₁
  have hp₂ := h.hp₂
  refine RelCT.seq (R := fun a b => E1 s₁ a ∧ E1 s₂ b) (relct_wp ?_ fun a b hab =>
    ⟨by rw [hab.1]; exact setup_ok hp₁, by rw [hab.2]; exact setup_ok hp₂⟩) ?_
  · exact taint_block [.r0, .r1, .r2] (fun a b hab r hr => by
      rw [hab.1, hab.2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.seed
      · exact h.a
      · exact h.scr) (by taint_decide)
  refine RelCT.seq (R := fun a b => E2 s₁ a ∧ E2 s₂ b) (relct_wp (absorbPhase_ct h) fun a b hab =>
    ⟨absorb_phase hp₁ hab.1.1 hab.1.2, absorb_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => E3 s₁ a ∧ E3 s₂ b) (relct_wp (padPhase_ct h) fun a b hab =>
    ⟨pad_phase hp₁ hab.1.1 hab.1.2.1 hab.1.2.2, pad_phase hp₂ hab.2.1 hab.2.2.1 hab.2.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => E4 s₁ a ∧ E4 s₂ b) (relct_wp (squeezePhase_ct h) fun a b hab =>
    ⟨squeeze_phase hp₁ hab.1.1 hab.1.2, squeeze_phase hp₂ hab.2.1 hab.2.2⟩) ?_
  refine RelCT.seq (R := fun a b => Inv s₁ 0 a ∧ Inv s₂ 0 b) (relct_wp ?_ fun a b hab =>
    ⟨init_ok hab.1.1 hab.1.2, init_ok hab.2.1 hab.2.2⟩) ?_
  · exact taint_block [.r5, .r6] (fun a b hab r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [hab.1.1.r5, hab.2.1.r5, h.a]
      · rw [hab.1.1.r6, hab.2.1.r6, h.scr]) (by taint_decide)
  refine RelCT.seq (R := fun a b => Inv s₁ 280 a ∧ Inv s₂ 280 b) (loop_ct h) ?_
  exact taint_block [.r6] (fun a b hab r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [hab.1.ls.env.r6, hab.2.ls.env.r6, h.scr]) (by taint_decide)

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlKem.sampleNTTContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h0, -, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem polyAt_toPoly {m : Mem} {p : Addr} {L : List Zq} (hl : L.length = n)
    (h : ∀ k < L.length, coeffAt m p k = BitVec.ofNat 32 (L.getD k 0).val) :
    PolyIs m p (VG.Proof.MlKem.toPoly L) := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [h i (by rw [hl]; exact hi), getElem!_eq _ hi]
  simp only [VG.Proof.MlKem.toPoly, Vector.getElem_ofFn]

theorem post_of {s₀ s : State}
    (h0 : s.gpr .r0 = (if (Ls s₀ 280).length = 256 then 1 else 0))
    (hc : ∀ k < (Ls s₀ 280).length, coeffAt s.mem (A s₀) k = BitVec.ofNat 32 ((Ls s₀ 280).getD k 0).val) :
    (Spec.MlKem.sampleNTTContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  by_cases hl : (Ls s₀ 280).length = 256
  · rw [ite_eq_left hl]
    have hpi := polyAt_toPoly (by rw [n_eq]; exact hl) hc
    refine ⟨fun _ => hpi.1, VG.Proof.MlKem.outcome_of_min (.inl ⟨rfl, ?_⟩)⟩
    have e2 : polyAt s.mem (BitVec.setWidth 64 (s₀.gpr .r1)) = _ := hpi.2
    rw [e2]
    exact VG.Proof.MlKem.sampleNTT_of_full (Nat.le_refl _) (by rw [n_eq]; exact hl)
  · rw [ite_eq_right hl]
    refine ⟨fun e => absurd e (by decide : (0 : BitVec 32) ≠ 1), VG.Proof.MlKem.outcome_of_min (.inr ⟨rfl, ?_⟩)⟩
    exact VG.Proof.MlKem.sampleNTT_none (by rw [n_eq]; exact hl)

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

theorem verified : Verified Arm.target Impl.MlKem.Arm.sampleNTT (Spec.MlKem.sampleNTTContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · have hp := pre_of hs
    obtain ⟨t, s', he, hpres, hsp, h0, hc⟩ := correct hp
    exact ⟨t, s', he, ⟨hpres, hsp⟩, post_of h0 hc⟩
  · have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    sig_pub [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
      Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2⟩ := hpub
    have two : Two s₁ s₂ := ⟨hp₁, hp₂, hsp, h0, h1, h2,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩
    exact (all_ct two s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlKem.sampleNTTContract, Spec.MlKem.sampleNTTSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlKem.Arm.Sample
