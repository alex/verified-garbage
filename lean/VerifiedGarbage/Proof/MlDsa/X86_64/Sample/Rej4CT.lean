import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Top
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlKem.X86_64.S4CT

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4_avx2`, constant time but for the seeds

Two runs whose seeds (the declared leak) and pointers agree leak the same. The
code but for the loops of the halves is proven by the taint analysis, from the
pointers (the prologue, the absorption and the first squeeze as in
`vg_mlkem_sample_ntt4_avx2`, `S4.start_ct`). Both runs read the same XOF
output, so in each half's loop they are at the same iteration with the same
coefficients sampled, and each iteration runs as in `vg_mldsa_rej_ntt_poly`
(`RejNttCT.body_ct`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem.X86_64.Sample4
open VG.Impl.MlDsa.X86_64.Sample (rnBody)
open VG.Impl.MlDsa.X86_64.Sample.Rej4 (oJ half first second zeroJ rejNTT4Avx2)
open VG.Proof.MlKem.X86_64 (sample4K relInv taintRel relStart Rel2 ofNat64_pred ofNat64_beq_zero RelCT.postDep)
open VG.Proof.MlKem.X86_64.S4 (R4 Pre aP at' pre_of pub_scr pub_aP pub_B env_rbx start_ct)
open VG.Proof.MlDsa.X86_64.Sample (nil_regs WP.all')
open VG.Proof.MlDsa.X86_64.Sample.RejNttCT (BPre BRel body_ct)
open VG.Spec.MlKem (poly4)

theorem pub_Lt4 {σ₁ σ₂ : State} (hq : sample4K.pub σ₁ σ₂) {K : Nat} (hK : K < 4) (t : Nat) :
    Lt σ₁ K t = Lt σ₂ K t := by simp only [Lt, Xb, pub_B hq hK]

/-! ## The squeezes -/

theorem sqTaint0 : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 0) hc).isSome = true := ⟨_, by taint_decide⟩
theorem sqTaint1 : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 1) hc).isSome = true := ⟨_, by taint_decide⟩
theorem sqTaint2 : ∃ hc : VG.Taint.Hint X86_64.Taint.T,
    (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 2) hc).isSome = true := ⟨_, by taint_decide⟩

/-- A squeeze, from the absorption, given its taint analysis. -/
theorem sqT_ct {t n : Nat} (hn : n < 3)
    (c : ∃ hc : VG.Taint.Hint X86_64.Taint.T, (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (R4 fun σ s => SqT σ t n s) (squeeze4 n) (R4 fun σ s => SqT σ t (n + 1) s) := by
  obtain ⟨_, c⟩ := c
  exact relInv (fun σ s hp h => WP.mono (sqT_ok (pre_of hp) hn h) fun _ h' => h'.1)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) c)

/-- A second squeeze, given its taint analysis. -/
theorem sqM_ct {n : Nat} (hn : n < 3)
    (c : ∃ hc : VG.Taint.Hint X86_64.Taint.T, (taint.check (X86_64.Taint.ofRegs [.rbx]) (squeeze4 n) hc).isSome = true) :
    RelCT isa (R4 fun σ s => M2 σ n s) (squeeze4 n) (R4 fun σ s => M2 σ (n + 1) s) := by
  obtain ⟨_, c⟩ := c
  exact relInv (fun σ s hp h => sqM_ok (pre_of hp) hn h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.sq.env h₂.sq.env) c)

/-! ## The halves -/

/-- Two runs at iteration `t` of a half of seed `K`, from states with `X`,
`n = 168 - t` iterations from its end. -/
def HI (X : State → State → Prop) (K h n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂ s₀₁ s₀₂ t, sample4K.pre σ₁ ∧ sample4K.pre σ₂ ∧ sample4K.pub σ₁ σ₂ ∧ n = 168 - t ∧ t < 168 ∧
    X σ₁ s₀₁ ∧ X σ₂ s₀₂ ∧ HAt σ₁ s₀₁ K h t s₁ ∧ HAt σ₂ s₀₂ K h t s₂

theorem hbpre {σ : State} (hp : Pre σ) {s₀ : State} {K h t : Nat} (hK : K < 4) (ht : t < 168) {s : State}
    (hI : HAt σ s₀ K h t s) : BPre s (poly4 (aP σ) K) (Lt σ K (168 * h + t)) :=
  ⟨hI.rbp, hI.rdi, Lt_length_le σ K _, coeffsWr hp hK hI.env, hI.stored,
    by simpa using hat_regions hp hK hI (j := 0) (by omega), hat_regions hp hK hI (by omega),
    hat_regions hp hK hI (by omega)⟩

theorem hi_brel {X : State → State → Prop} {K h n : Nat} (hK : K < 4) (hh : h < 2) {s₁ s₂ : State}
    (H : HI X K h n s₁ s₂) : BRel s₁ s₂ := by
  obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, _, ht, _, _, l₁, l₂⟩ := H
  refine ⟨poly4 (aP σ₁) K, Lt σ₁ K (168 * h + t), hbpre (pre_of p₁) hK ht l₁,
    by rw [pub_aP hq, pub_Lt4 hq hK]; exact hbpre (pre_of p₂) hK ht l₂,
    by rw [l₁.rsi, l₂.rsi, at', at', pub_scr hq], by rw [l₁.rcx, l₂.rcx], fun k hk => ?_⟩
  rw [hat_byte hh l₁ (by omega), hat_byte hh l₂ (by omega)]
  simp only [Xb, pub_B hq hK]

/-- The loop of a half. -/
theorem hloop_ct {X : State → State → Prop} {K h : Nat} (hK : K < 4) (hh : h < 2) (n : Nat) :
    RelCT isa (HI X K h n) (.loop rnBody .ne) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h 168 s) := by
  refine RelCT.loop (M := isa) (HI X K h) (fun n => ?_) n
  refine RelCT.postDep (F := fun (x x' : State) => ∀ p : State × State × Nat, sample4K.pre p.1 ∧ p.2.2 < 168 ∧
      HAt p.1 p.2.1 K h p.2.2 x →
        HAt p.1 p.2.1 K h (p.2.2 + 1) x' ∧ x'.zf = some (BitVec.ofNat 64 (168 - p.2.2) - 1 == 0))
    (RelCT.mono body_ct (fun x y H => hi_brel hK hh H) fun _ _ _ => trivial) (fun x y H => ?_) ?_
  · obtain ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, _, _, ht, _, _, l₁, l₂⟩ := H
    exact ⟨WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hp'.2.1 hp'.2.2) ⟨(σ₁, s₀₁, t), p₁, ht, l₁⟩,
      WP.all' (fun p hp' => hat_step (pre_of hp'.1) hK hh hp'.2.1 hp'.2.2) ⟨(σ₂, s₀₂, t), p₂, ht, l₂⟩⟩
  · intro x y x' y' ⟨σ₁, σ₂, s₀₁, s₀₂, t, p₁, p₂, hq, hn, ht, x₁, x₂, l₁, l₂⟩ f₁ f₂
    obtain ⟨l₁', z₁⟩ := f₁ (σ₁, s₀₁, t) ⟨p₁, ht, l₁⟩
    obtain ⟨l₂', z₂⟩ := f₂ (σ₂, s₀₂, t) ⟨p₂, ht, l₂⟩
    have ez : (BitVec.ofNat 64 (168 - t) - 1 == 0) = decide (t + 1 = 168) := by
      rw [ofNat64_pred (by omega) (by omega), ofNat64_beq_zero (by omega)]
      exact decide_eq_decide.mpr (by omega)
    rw [ez] at z₁ z₂
    refine ⟨by show x'.zf.map _ = y'.zf.map _; rw [z₁, z₂], fun hf => ?_, fun ht' => ?_⟩
    · have : t + 1 = 168 := by
        have : x'.zf.map (!·) = some false := hf
        rw [z₁] at this; simpa using this
      rw [this] at l₁' l₂'
      exact ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁'⟩, ⟨s₀₂, x₂, l₂'⟩⟩
    · have : t + 1 ≠ 168 := by
        have : x'.zf.map (!·) = some true := ht'
        rw [z₁] at this; simpa using this
      exact ⟨168 - (t + 1), by omega, σ₁, σ₂, s₀₁, s₀₂, t + 1, p₁, p₂, hq, rfl, by omega, x₁, x₂, l₁', l₂'⟩

/-- The setup of a half. -/
abbrev hsetup (K : Nat) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * K))),
    .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * K))),
    .mov .rdi (.mem (at_ .rbx (oJ + 8 * K))), .mov32 .rcx (.imm 168)]

/-- A half of seed `K` from states with `X`, given the taint analysis of its setup. -/
theorem half_ct {X : State → State → Prop} {K h : Nat} (hK : K < 4) (hh : h < 2)
    (hX : ∀ σ s, sample4K.pre σ → X σ s → HPre σ K h s) {hc : VG.Taint.Hint X86_64.Taint.T}
    (c : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (hsetup K)) hc).isSome = true) :
    RelCT isa (R4 X) (half K) (R4 fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h 168 s) := by
  unfold half
  refine RelCT.seq (RelCT.mono (relInv (I' := fun σ s => ∃ s₀, X σ s₀ ∧ HAt σ s₀ K h 0 s)
      (fun σ s hp hx => WP.mono (hsetup_ok (pre_of hp) hK (hX σ s hp hx)) fun _ h' => ⟨s, hx, h'⟩)
      (taintRel [.rbx, .r13] (fun x y ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ r hr => by
        have e₁ := (hX σ₁ x p₁ h₁).env
        have e₂ := (hX σ₂ y p₂ h₂).env
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact env_rbx hq e₁ e₂
        · rw [e₁.r13, e₂.r13, pub_aP hq]) c)) (fun _ _ h => h)
      (Q' := HI X K h 168) fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, ⟨s₀₁, x₁, l₁⟩, ⟨s₀₂, x₂, l₂⟩⟩ =>
        ⟨σ₁, σ₂, s₀₁, s₀₂, 0, p₁, p₂, hq, rfl, by decide, x₁, x₂, l₁, l₂⟩) (hloop_ct hK hh 168)

/-- The first half of seed `K`, given the taint analysis of its blocks. -/
theorem first_ct {K : Nat} (hK : K < 4) {h₁ h₂ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (hsetup K)) h₁).isSome = true)
    (c₂ : (taint.check (X86_64.Taint.ofRegs [.rbx]) (.block [.store (at_ .rbx (oJ + 8 * K)) .rdi]) h₂).isSome =
      true) :
    RelCT isa (R4 fun σ s => P1 σ K s) (first K) (R4 fun σ s => P1 σ (K + 1) s) :=
  RelCT.seq (half_ct hK (by decide) (fun _ _ _ h => hpre1 hK h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => firstEnd_ok (pre_of hp) hK h₀ hA)
      (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, ⟨_, _, a₁⟩, ⟨_, _, a₂⟩⟩ r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq a₁.env a₂.env) c₂))

/-- The second half of seed `K`, given the taint analysis of its setup. -/
theorem second_ct {K : Nat} (hK : K < 4) {h₁ : VG.Taint.Hint X86_64.Taint.T}
    (c₁ : (taint.check (X86_64.Taint.ofRegs [.rbx, .r13]) (.block (hsetup K)) h₁).isSome = true) :
    RelCT isa (R4 fun σ s => P2 σ K s) (second K) (R4 fun σ s => P2 σ (K + 1) s) :=
  RelCT.seq (half_ct hK (by decide) (fun _ _ _ h => hpre2 hK h) c₁)
    (relInv (fun σ s hp ⟨_, h₀, hA⟩ => secondEnd_ok (pre_of hp) hK h₀ hA) (taintRel [] nil_regs (by taint_decide)))

/-! ## The whole function -/

theorem ct : ConstantTime isa r4K.pre r4K.pub rejNTT4Avx2 := by
  refine relStart (Q := fun _ _ => True) (RelCT.seq start_ct (RelCT.seq (RelCT.mono (sqT_ct (t := 0) (by decide) sqTaint0)
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, sqT_of h₁, sqT_of h₂⟩) fun _ _ h => h)
    (RelCT.seq (sqT_ct (by decide) sqTaint1) (RelCT.seq (sqT_ct (by decide) sqTaint2) ?_))))
  refine RelCT.seq (relInv (fun σ s hp h => zeroJ_ok (pre_of hp) h)
    (taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide))) ?_
  refine RelCT.seq (first_ct (K := 0) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (first_ct (K := 1) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (first_ct (K := 2) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (first_ct (K := 3) (by decide) (by taint_decide) (by taint_decide)) ?_
  refine RelCT.seq (RelCT.mono (sqM_ct (by decide) sqTaint0)
    (fun _ _ ⟨σ₁, σ₂, p₁, p₂, hq, h₁, h₂⟩ => ⟨σ₁, σ₂, p₁, p₂, hq, m2_of h₁, m2_of h₂⟩) fun _ _ h => h)
    (RelCT.seq (sqM_ct (by decide) sqTaint1) (RelCT.seq (sqM_ct (by decide) sqTaint2) ?_))
  refine RelCT.seq (relInv (fun σ s _ h => vz_ok h) (taintRel [] nil_regs (by taint_decide))) ?_
  refine RelCT.seq (second_ct (K := 0) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (second_ct (K := 1) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (second_ct (K := 2) (by decide) (by taint_decide)) ?_
  refine RelCT.seq (second_ct (K := 3) (by decide) (by taint_decide)) ?_
  exact taintRel [.rbx] (fun x y ⟨σ₁, σ₂, _, _, hq, h₁, h₂⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact env_rbx hq h₁.env h₂.env) (by taint_decide)

end VG.Proof.MlDsa.X86_64.Rej4
