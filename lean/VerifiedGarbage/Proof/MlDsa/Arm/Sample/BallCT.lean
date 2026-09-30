import VerifiedGarbage.Proof.MlDsa.Arm.Sample.Ball

/-!
# ML-DSA on 32-bit ARM: `vg_mldsa_sample_in_ball`, constant time but for `c̃`, and `Verified`

Untrusted: everything here is checked by Lean. Two runs whose `c̃` (the
declared leak), `len`, `τ`, pointers and stack pointer agree (`Two`) leak
the same: the prologue by `relct_ldrSp` (the load of `scratch` from the
stack) and the taint analysis, the sponge by `sponge_ct`, the blocks around
the loop by the taint analysis, and the loop, whose branches and addresses
depend on the SHAKE256 output, by relating the two runs iteration by
iteration (`body_ct`): both are at the same iteration with the same `i`,
sign bits and byte `j` (being those of the same output), so each branch
goes the same way, and each piece between the branches is constant time in
registers that hold the same values in both runs.
-/

namespace VG.Proof.MlDsa.Arm.Sample.Ball

open VG VG.Arm
open VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.Sample
open VG.Impl.MlDsa.Arm.Sample
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq q H IPoly n ofInt coeffAt PolyIs toRq)
open VG.Spec.Sha3 (bytesAt)
open VG.Arm.RegUpd (gpr_setReg_self gpr_setReg_of_ne)

/-! ## Blocks -/

/-- A block in two parts. -/
theorem relct_append {P R Q : State → State → Prop} {l₁ l₂ : List Instr} (h₁ : RelCT isa P (.block l₁) R)
    (h₂ : RelCT isa R (.block l₂) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff, execBlock_append] at e₁ e₂
  obtain ⟨⟨u₁, v₁⟩, a₁, e₁⟩ := Option.bind_eq_some_iff.mp e₁
  obtain ⟨⟨w₁, x₁⟩, b₁, e₁⟩ := Option.map_eq_some_iff.mp e₁
  obtain ⟨⟨u₂, v₂⟩, a₂, e₂⟩ := Option.bind_eq_some_iff.mp e₂
  obtain ⟨⟨w₂, x₂⟩, b₂, e₂⟩ := Option.map_eq_some_iff.mp e₂
  obtain ⟨rfl, r⟩ := h₁ _ _ _ _ _ _ hp (.block a₁) (.block a₂)
  obtain ⟨rfl, q⟩ := h₂ _ _ _ _ _ _ r (.block b₁) (.block b₂)
  cases e₁; cases e₂
  exact ⟨rfl, q⟩

/-- The load of an argument from the stack leaks its address. -/
theorem relct_ldrSp {P : State → State → Prop} {t : Reg} {off : Nat} (hsp : ∀ a b, P a b → a.sp = b.sp) :
    RelCT isa P (.block [.ldrSp t off]) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  have tr : ∀ {s s' : State} {tr : List Leak}, execBlock isa [.ldrSp t off] s = some (s', tr) →
      tr = [Leak.addr (State.addr (s.sp + BitVec.ofNat 32 off))] := fun {s s' tr} e => by
    simp only [execBlock] at e
    split at e
    · cases e
    · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      rw [← e.2]; rfl
  rw [tr e₁, tr e₂, hsp _ _ hp]
  exact ⟨rfl, trivial⟩

theorem ldrSp_ok (σ : State) (hin : InRegions (σ.rd ++ σ.wr) (stackArgAddr σ 0) 4) :
    WP isa (.block [.ldrSp .r12 0]) σ fun s => s = σ.setReg .r12 (stackArg σ 0) := by
  have hin' : InRegions (σ.rd ++ σ.wr) (State.addr (σ.sp + BitVec.ofNat 32 0)) 4 := hin
  have o0 : (0 : Nat) < 4096 := by decide
  apply WP.of_runBlock
  rw [runBlock_cons]
  simp only [exec, o0, ite_true, State.load32, hin', Option.map_some, runStep_some, runBlock_nil]
  exact ⟨_, rfl, rfl⟩

/-! ## Two runs -/

/-- Two runs, from entry states that agree on the public data. -/
structure Two (σ₁ σ₂ : State) : Prop where
  p₁ : Pre σ₁
  p₂ : Pre σ₂
  sp : σ₁.sp = σ₂.sp
  r0 : σ₁.gpr .r0 = σ₂.gpr .r0
  r1 : σ₁.gpr .r1 = σ₂.gpr .r1
  r2 : σ₁.gpr .r2 = σ₂.gpr .r2
  r3 : σ₁.gpr .r3 = σ₂.gpr .r3
  scr : stackArg σ₁ 0 = stackArg σ₂ 0
  B : B σ₁ = B σ₂

section
variable {σ₁ σ₂ : State} (two : Two σ₁ σ₂)
include two

theorem Two.P_eq : spOf σ₁ = spOf σ₂ := by simp only [spOf, two.r0, two.r1, two.r2, two.r3, two.scr]
theorem Two.X_eq : X σ₁ = X σ₂ := by simp only [X, two.B]
theorem Two.tau_eq : tau σ₁ = tau σ₂ := by simp only [tau, two.r2]
theorem Two.St_eq (t : Nat) : St σ₁ t = St σ₂ t := by simp only [St, i0, two.X_eq, two.tau_eq]
theorem Two.Xb_eq (t : Nat) : Xb σ₁ t = Xb σ₂ t := by simp only [Xb, two.X_eq]
theorem Two.Wn_eq : Wn σ₁ = Wn σ₂ := by simp only [Wn, two.X_eq]

/-- The sign bits not yet used, in both runs. -/
theorem Two.sg_eq {i : Nat} {a b : State} (ha : Sg σ₁ i a) (hb : Sg σ₂ i b) :
    a.gpr .r1 = b.gpr .r1 ∧ a.gpr .r4 = b.gpr .r4 := by
  have ha' : (a.gpr .r1).toNat + 2 ^ 32 * (a.gpr .r4).toNat = Wn σ₁ / 2 ^ (i - i0 σ₁) := ha
  have hb' : (b.gpr .r1).toNat + 2 ^ 32 * (b.gpr .r4).toNat = Wn σ₂ / 2 ^ (i - i0 σ₂) := hb
  rw [← two.Wn_eq, show i0 σ₂ = i0 σ₁ by simp only [i0, two.tau_eq]] at hb'
  have := (a.gpr .r1).isLt; have := (b.gpr .r1).isLt
  exact ⟨BitVec.eq_of_toNat_eq (by omega), BitVec.eq_of_toNat_eq (by omega)⟩

/-! ## The loop -/

omit two in
theorem pieceA_ct {t : Nat} : RelCT isa (fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) (.block jFull)
    fun a b => M1 σ₁ t a ∧ M1 σ₂ t b :=
  relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun a b h => ⟨pieceA h.1, pieceA h.2⟩

theorem tryA_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => (M1 σ₁ t a ∧ M1 σ₂ t b) ∧ isa.eval .eq a = some false)
      (.block [.ldrb .r8 .r0 0, .dp .sub .r11 .r2 (.reg .r8), .mov .r11 (.shifted .r11 .lsr 31),
        .cmp .r11 (.imm 0)]) fun a b => T1 σ₁ t a ∧ T1 σ₂ t b := by
  refine relW (taintRel [.r0] (fun a b h r hr => ?_) (by taint_decide)) fun a b h => ?_
  · rw [List.mem_singleton] at hr; subst hr
    rw [h.1.1.bat.r0, h.1.2.bat.r0, two.scr]
  · have za : a.z = false := Option.some.inj h.2
    have zb : b.z = false := by
      rw [h.1.2.z, ← two.St_eq, ← h.1.1.z]; exact za
    exact ⟨tryA two.p₁.ok ht h.1.1 za, tryA two.p₂.ok ht h.1.2 zb⟩

theorem set_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => (T1 σ₁ t a ∧ T1 σ₂ t b) ∧ isa.eval .eq a = some true) bSet
      fun a b => M2 σ₁ t a ∧ M2 σ₂ t b := by
  refine relW (taintRel [.r1, .r2, .r4, .r5, .r8] (fun a b h r hr => ?_) (by taint_decide)) fun a b h => ?_
  · have l₁ := h.1.1.bat
    have l₂ := h.1.2.bat
    have sg := two.sg_eq (two.St_eq t ▸ l₁.sg) l₂.sg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact sg.1
    · rw [l₁.r2, l₂.r2, two.St_eq]
    · exact sg.2
    · rw [l₁.env.r5, l₂.env.r5, two.P_eq]
    · rw [h.1.1.r8, h.1.2.r8, two.Xb_eq]
  · have za : a.z = true := Option.some.inj h.2
    have zb : b.z = true := by
      rw [h.1.2.z, ← two.St_eq, ← two.Xb_eq, ← h.1.1.z]; exact za
    have h1 := two.p₁.tau_le
    have h2 := two.p₂.tau_le
    exact ⟨setOk two.p₁.ok (by omega) ht h.1.1 za, setOk two.p₂.ok (by omega) ht h.1.2 zb⟩

omit two in
theorem nil_ct {P : State → State → Prop} {Q₁ Q₂ : State → Prop} (hq : ∀ a b, P a b → Q₁ a ∧ Q₂ b) :
    RelCT isa P (.block []) fun a b => Q₁ a ∧ Q₂ b :=
  relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
    fun a b h => ⟨WP.block_nil (hq a b h).1, WP.block_nil (hq a b h).2⟩

omit two in
theorem skip_of {σ : State} {t : Nat} (ht : t < 264) {s : State} (h : T1 σ t s) (e : s.z = false) :
    M2 σ t s := by
  have hj : (St σ t).2 < (Xb σ t).toNat := by
    have := h.z; rw [e] at this; exact Nat.lt_of_not_le (of_decide_eq_false this.symm)
  have hst := St_succ σ ht
  rw [bStep, ifT h.lt, ifT hj] at hst
  exact M2.of_same h.bat hst

omit two in
theorem full_of {σ : State} {t : Nat} (ht : t < 264) {s : State} (h : M1 σ t s) (e : s.z = true) :
    M2 σ t s := by
  have hl : (St σ t).2 = 256 := by
    have := h.z; rw [e] at this; simp at this; have := St_le σ t; omega
  exact M2.of_same h.bat (by rw [St_succ σ ht, bStep_full hl])

theorem body_ct {t : Nat} (ht : t < 264) :
    RelCT isa (fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) bBody fun a b =>
      (BAt σ₁ (t + 1) a ∧ a.z = decide (t + 1 = 264)) ∧ (BAt σ₂ (t + 1) b ∧ b.z = decide (t + 1 = 264)) := by
  refine RelCT.seq pieceA_ct (RelCT.seq (R := fun a b => M2 σ₁ t a ∧ M2 σ₂ t b) ?_ ?_)
  · refine RelCT.ite (fun a b h => by show some a.z = some b.z; rw [h.1.z, h.2.z, two.St_eq]) ?_ ?_
    · exact nil_ct fun a b h => ⟨full_of ht h.1.1 (Option.some.inj h.2), full_of ht h.1.2 (by
        rw [h.1.2.z, ← two.St_eq, ← h.1.1.z]; exact Option.some.inj h.2)⟩
    · refine RelCT.seq (tryA_ct two ht) (RelCT.ite (fun a b h => by
        show some a.z = some b.z; rw [h.1.z, h.2.z, two.St_eq, two.Xb_eq]) (set_ct two ht) ?_)
      exact nil_ct fun a b h => ⟨skip_of ht h.1.1 (Option.some.inj h.2), skip_of ht h.1.2 (by
        rw [h.1.2.z, ← two.St_eq, ← two.Xb_eq, ← h.1.1.z]; exact Option.some.inj h.2)⟩
  · exact relW (taintRel [] (fun _ _ _ _ h => absurd h List.not_mem_nil) (by taint_decide))
      fun a b h => ⟨pieceC ht h.1, pieceC ht h.2⟩

theorem loop_ct : RelCT isa (fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b) (.loop bBody .ne) fun a b =>
    BAt σ₁ 264 a ∧ BAt σ₂ 264 b := by
  refine RelCT.mono (RelCT.loop (M := isa) (body := bBody) (c := .ne)
    (Q := fun a b => BAt σ₁ 264 a ∧ BAt σ₂ 264 b)
    (fun n a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b) (fun n => ?_) 264)
    (fun a b hab => ⟨0, by decide, rfl, hab⟩) (fun _ _ h => h)
  refine RelCT.mono (P := fun a b => ∃ t, t < 264 ∧ n = 264 - t ∧ BAt σ₁ t a ∧ BAt σ₂ t b)
    (RelCT.exists_ fun t => ?_) (fun _ _ hab => hab) (fun _ _ h => h)
  by_cases ht : t < 264
  · by_cases hn : n = 264 - t
    · refine RelCT.mono (P := fun a b => BAt σ₁ t a ∧ BAt σ₂ t b) (body_ct two ht) (fun _ _ hab => hab.2.2)
        fun a b ⟨⟨i₁, z₁⟩, ⟨i₂, z₂⟩⟩ => ⟨?_, fun e => ?_, fun e => ?_⟩
      · show some (!a.z) = some (!b.z); rw [z₁, z₂]
      · have : t + 1 = 264 := by
          have e' : (!a.z) = false := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        rw [this] at i₁ i₂; exact ⟨i₁, i₂⟩
      · have : t + 1 ≠ 264 := by
          have e' : (!a.z) = true := Option.some.inj e
          rw [z₁] at e'; simpa using e'
        exact ⟨264 - (t + 1), by omega, t + 1, by omega, rfl, i₁, i₂⟩
    · exact RelCT.of_false fun _ _ hab => hn hab.2.1
  · exact RelCT.of_false fun _ _ hab => ht hab.1

/-! ## The whole function -/

theorem pro_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂)
    (.block (.ldrSp .r12 0 :: pro .r12 .r3 (.reg .r2) (.reg .r1) .r0))
    fun a b => J0 (spOf σ₁) σ₁ a ∧ J0 (spOf σ₂) σ₂ b := by
  refine relW ?_ fun a b h => ⟨by rw [h.1]; exact pro_ball two.p₁.ok rfl (by simp) rfl rfl rfl two.p₁.arg,
    by rw [h.2]; exact pro_ball two.p₂.ok rfl (by simp) rfl rfl rfl two.p₂.arg⟩
  show RelCT isa _ (.block ([.ldrSp .r12 0] ++ pro .r12 .r3 (.reg .r2) (.reg .r1) .r0)) _
  refine relct_append (R := fun a b => a = σ₁.setReg .r12 (stackArg σ₁ 0) ∧ b = σ₂.setReg .r12 (stackArg σ₂ 0))
    (relct_ldrSp (fun a b h => by rw [h.1, h.2, two.sp]) |>.wp (F₁ := fun s => s = σ₁.setReg .r12 (stackArg σ₁ 0))
      (F₂ := fun s => s = σ₂.setReg .r12 (stackArg σ₂ 0))
      (fun a b h => ⟨by rw [h.1]; exact ldrSp_ok σ₁ two.p₁.arg, by rw [h.2]; exact ldrSp_ok σ₂ two.p₂.arg⟩)
      |>.mono (fun _ _ h => h) fun _ _ h => h.2) ?_
  refine taintRel [.r0, .r1, .r2, .r3, .r12] (fun a b h r hr => ?_) (by taint_decide)
  rw [h.1, h.2]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r0
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r1
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r2
  · rw [gpr_setReg_of_ne _ _ (by decide), gpr_setReg_of_ne _ _ (by decide)]; exact two.r3
  · rw [gpr_setReg_self, gpr_setReg_self]; exact two.scr

theorem all_ct : RelCT isa (fun a b => a = σ₁ ∧ b = σ₂) Impl.MlDsa.Arm.Sample.sampleInBall fun _ _ => True := by
  have hP := two.P_eq
  have ok₂ : SpOk (spOf σ₁) σ₂ := hP ▸ two.p₂.ok
  refine RelCT.seq (pro_ct two) ?_
  refine RelCT.seq (R := fun a b => J6 136 272 (spOf σ₁) σ₁ a ∧ J6 136 272 (spOf σ₂) σ₂ b)
    ((sponge_ct two.p₁.ok ok₂ two.sp (rate := 136) (outlen := 272) (by decide) (by decide) (by decide) (by decide)
      (by taint_decide) (by taint_decide) (by taint_decide)).mono (fun a b h => ⟨h.1, hP ▸ h.2⟩)
      fun a b h => ⟨h.1, hP ▸ h.2⟩) ?_
  refine RelCT.seq (R := fun a b => ZDone σ₁ a ∧ ZDone σ₂ b) (relW (taintRel [.r5] (fun a b h r hr => by
      rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r5, h.2.env.r5, hP]) (by taint_decide))
    fun a b h => ⟨zero_ok two.p₁.ok h.1, zero_ok two.p₂.ok h.2⟩) ?_
  have t₁ : tau σ₁ ≤ 256 := by have := two.p₁.tau_le; omega
  have t₂ : tau σ₂ ≤ 256 := by have := two.p₂.tau_le; omega
  refine RelCT.seq (RelCT.seq (R := fun a b => BAt σ₁ 0 a ∧ BAt σ₂ 0 b) (relW (taintRel [.r6, .r7]
      (fun a b h r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [h.1.env.r6, h.2.env.r6, hP]
        · rw [h.1.r7, h.2.r7, two.r2]) (by taint_decide))
    fun a b h => ⟨setup_ok two.p₁.ok t₁ h.1, setup_ok two.p₂.ok t₂ h.2⟩) (loop_ct two)) ?_
  exact taintRel [.r6] (fun a b h r hr => by
    rw [List.mem_singleton] at hr; subst hr; rw [h.1.env.r6, h.2.env.r6, hP]) (by taint_decide)

end

/-! ## Verified -/

theorem pre_of {s : State} (h : (Spec.MlDsa.sampleInBallContract Arm.abi 8).pre s) : Pre s := by
  sig_pre [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val] at h
  obtain ⟨h8, -, hrd, hwr, d1, d2, d3, -, -, b1, b2, b3, -, f1, f2, f3, hb⟩ := h
  simp only [Spec.MlDsa.ballParams, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
  exact ⟨⟨by rw [hrd]; exact List.mem_cons.mpr (.inl rfl), hwr, d1, d2, d3, b1, b2, b3, f1, (s.gpr .r1).isLt, f2, f3, h8⟩,
    ⟨_, by rw [hrd]; exact List.mem_append_left _ (List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))),
      Region.contains_self _ _⟩, by simp only [tau]; omega, by simp only [tau]; omega⟩

theorem post_of {s₀ s : State}
    (h0 : s.gpr .r0 = (if (ballFold (tau s₀) (X s₀)).2 = 256 then 1 else 0))
    (hc : (ballFold (tau s₀) (X s₀)).2 = 256 →
      PolyIs s.mem (State.addr (s₀.gpr .r3)) (toRq (ballFold (tau s₀) (X s₀)).1)) :
    (Spec.MlDsa.sampleInBallContract Arm.abi 8).post s₀ s := by
  sig_post [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val]
  rw [setWidth_append32, h0]
  by_cases hf : (ballFold (tau s₀) (X s₀)).2 = 256
  · rw [ifT hf]
    obtain ⟨hred, hpoly⟩ := hc hf
    exact ⟨fun _ => hred, .inl ⟨rfl, { Spec.MlDsa.minBounds with ball := 272 }, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 272 (B s₀)) =
        some (Spec.MlDsa.polyAt s.mem (State.addr (s₀.gpr .r3)))
      rw [sampleInBall_some _ (by decide) hf]
      exact congrArg some hpoly.symm⟩⟩
  · rw [ifF hf]
    exact ⟨fun h1 => absurd h1 (by decide), .inr ⟨rfl, by
      show Option.map toRq (Spec.MlDsa.sampleInBall (tau s₀) 221 (B s₀)) = none
      rw [sampleInBall_none _ (B := 272) (by decide) (by decide) hf]; rfl⟩⟩

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 32 | .r2 => 39 | .r3 => 0x2000 | _ => 0
  sp := 0x8000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x8001 then 0x30 else 0
  rd := [⟨0x1000, 32⟩, ⟨0x8000, 4⟩]
  wr := [⟨0x2000, 1024⟩, ⟨0x3000, 2048⟩]

end VG.Proof.MlDsa.Arm.Sample.Ball

namespace VG.Proof.MlDsa.Arm.Sample

open VG VG.Arm
open Ball

theorem sampleInBall_verified :
    Verified Arm.target Impl.MlDsa.Arm.Sample.sampleInBall (Spec.MlDsa.sampleInBallContract Arm.abi 8) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, ?_⟩
  · obtain ⟨t, s', he, h0, hc, hpres⟩ := correct (pre_of hs)
    exact ⟨t, s', he, hpres, post_of h0 hc⟩
  · sig_pub [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val] at hpub
    obtain ⟨hsp, hb, h0, h1, h2, h3, hs⟩ := hpub
    have two : Two s₁ s₂ := ⟨pre_of h₁, pre_of h₂, hsp, h0, h1, h2, h3, hs,
      (List.map_inj_right (fun x y (e : x.toNat = y.toNat) => BitVec.eq_of_toNat_eq e)).mp hb⟩
    exact (all_ct two s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂).1
  · refine ⟨satState, ?_⟩
    sig_sat_check [Spec.MlDsa.sampleInBallContract, Spec.MlDsa.sampleInBallSig, Arm.abi, Arm.argRegs,
      Arm.reduceClassify, Arm.Loc.val]

end VG.Proof.MlDsa.Arm.Sample
