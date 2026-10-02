import VerifiedGarbage.Proof.CmacAes.Arm.UpdateCorrect
import VerifiedGarbage.Proof.Framework.Arm.ArgTaint

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_update` is constant time

The taint analysis does not analyse frames, so two runs from states that agree
on the public arguments are related piece by piece (`RelCT`): the taint
analysis covers the code between the calls, from the public arguments for the
prologue and from the registers the correctness proof pins to them (`LInv`)
afterwards, and each call of `vg_aes_ctr32`, in its frame, is constant time by
its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (eval_eq eval_ne)

/-- The registers holding our variables in the loop. -/
abbrev vars : List Reg := [.r4, .r5, .r6, .r7, .r8, .r10]

section
variable {s₀ s₀' : State} (hq : updateArm.pub s₀ s₀')
include hq

theorem pub_sp : s₀.sp = s₀'.sp := hq.1
theorem pub_W : W s₀ = W s₀' := hq.2.1
theorem pub_r1 : s₀.gpr .r1 = s₀'.gpr .r1 := hq.2.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_r1 hq]
theorem pub_St : St s₀ = St s₀' := hq.2.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.2
theorem pub_Cb : Cb s₀ = Cb s₀' := by rw [Cb, Cb, pub_S hq]

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv s₀ k s₁) (h₂ : LInv s₀' k s₂) :
    ∀ r ∈ vars, s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [vars, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.r4, h₂.r4, pub_W hq]
  · rw [h₁.r5, h₂.r5, pub_r1 hq]
  · rw [h₁.r6, h₂.r6, pub_St hq]
  · rw [h₁.r7, h₂.r7, pub_Dp hq]
  · rw [h₁.r8, h₂.r8, pub_N hq]
  · rw [h₁.r10, h₂.r10, pub_S hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (Cb s₀) (St s₀) (S s₀) (R s₀) .r9 .r10
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem bodyMid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.keep .r7 (by decide) (by decide) (by decide) (by decide) (by decide), h.r7],
      by rw [hb.keep .r8 (by decide) (by decide) (by decide) (by decide) (by decide), h.r8],
      by rw [hb.sp, h.sp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r7 : s.gpr .r7 = Dp s₀ + BitVec.ofNat 32 (16 * k)
  r8 : s.gpr .r8 = BitVec.ofNat 32 (N s₀ - k)

theorem call_after {s₀ : State} {k : Nat} {s : State} (h : Mid s₀ k s) :
    WP isa (ctrCall .r9 .r10) s (After s₀ k) :=
  WP.mono (ctr_call h.pre) fun _ hc =>
    ⟨by rw [hc.saved .r7 (by simp [preserved]) (by decide), h.r7],
      by rw [hc.saved .r8 (by simp [preserved]) (by decide), h.r8]⟩

/-- The relation before a block, in two runs. -/
def BRel (s₀ s₀' : State) (k : Nat) (s₁ s₂ : State) : Prop :=
  (k < N s₀ ∧ LInv s₀ k s₁) ∧ (k < N s₀' ∧ LInv s₀' k s₂)

theorem body_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateArm.pub s₀ s₀') (k : Nat) :
    RelCT isa (BRel s₀ s₀' k) body fun _ _ => True := by
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r7, .r8]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := rel_agree (F := fun s => k < N s₀ ∧ LInv s₀ k s) (F' := fun s => k < N s₀' ∧ LInv s₀' k s)
    (G := Mid s₀ k) (G' := Mid s₀' k) (Taint.ofRegs vars)
    (fun _ _ h h' => Taint.agree_ofRegs (LInv.agree hq h.2 h'.2)) ⟨_, by taint_decide⟩
    (fun _ h => bodyMid_wp hp h.1 h.2) (fun _ h => bodyMid_wp hp' h.1 h.2)
  have c := rel_wp (F := Mid s₀ k) (F' := Mid s₀' k) (G := After s₀ k) (G' := After s₀' k)
    (ctr_rel (sp₀ := s₀.sp) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_Cb hq, pub_St hq, pub_S hq, pub_R hq]; exact h.2.pre, h.1.sp,
        h.2.sp.trans (pub_sp hq).symm⟩)
    (fun _ h => call_after h) (fun _ h => call_after h)
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) (Taint.ofRegs [.r7, .r8])
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r7, h.2.r7, pub_Dp hq]
      · rw [h.1.r8, h.2.r8, pub_N hq]) hB
  exact a.seq (c.seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ BRel s₀ s₀' k s₁ s₂

theorem loop_ct {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀') (hq : updateArm.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop body .ne) fun s₁ s₂ => LInv s₀ (N s₀) s₁ ∧ LInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  have ct := (body_ct hp hp' hq k).wp
    (F₁ := fun (s : State) => (LInv s₀ (k + 1) s ∧ s.z = decide (N s₀ - (k + 1) = 0)) ∧ k < N s₀)
    (F₂ := fun (s : State) => LInv s₀' (k + 1) s ∧ s.z = decide (N s₀' - (k + 1) = 0))
    fun _ _ h => ⟨WP.mono (body_ok hp h.1.1 h.1.2) fun _ r => ⟨r, h.1.1⟩, body_ok hp' h.2.1 h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨⟨l₁, z₁⟩, hk⟩, ⟨l₂, z₂⟩⟩ => ?_
  have e₁ : isa.eval .ne s₁ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₁ = _; rw [eval_ne, z₁]
  have e₂ : isa.eval .ne s₂ = some !decide (N s₀ - (k + 1) = 0) := by
    show VG.Arm.eval .ne s₂ = _; rw [eval_ne, z₂, ← hN]
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, ⟨by omega, l₁⟩, ⟨by omega, l₂⟩⟩

/-! ## The whole function -/

theorem update_rel {s₀ s₀' : State} (h0 : updateArm.pre s₀) (h0' : updateArm.pre s₀')
    (hq : updateArm.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') update fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (argTaint [.r0, .r1, .r2, .r3] 8) (.block (save ++ setup)) h).isSome =
      true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r10]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have hN := pub_N hq
  have hsp := pub_sp hq
  have wfA : ∀ {s : State}, UPre s →
      s.sp.toNat + 8 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 8⟩ r := fun {s} h => by
    have e : (⟨State.addr s.sp, 8⟩ : Region) = argsR s := by simp [stackArgAddr]
    refine ⟨h.sp_fit, ?_⟩
    rw [e, h.wr]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact h.st_args.symm
    · exact h.scr_args.symm
  have pro := rel_agree (F := fun s => s = s₀) (F' := fun s => s = s₀')
    (G := fun s => LInv s₀ 0 s ∧ s.z = decide (N s₀ = 0)) (G' := fun s => LInv s₀' 0 s ∧ s.z = decide (N s₀' = 0))
    (argTaint [.r0, .r1, .r2, .r3] 8)
    (fun s s' e e' => by
      subst e e'
      refine agree_argTaint (fun r hr => ?_) hsp (wfA hp) (wfA hp')
        (argMem_of (j := 2) hsp hp.sp_fit fun i hi => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact hq.2.1
        · exact hq.2.2.1
        · exact hq.2.2.2.1
        · exact hq.2.2.2.2.1
      · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · exact hq.2.2.2.2.2.1
        · exact hq.2.2.2.2.2.2) ⟨_, hpro⟩
    (fun s e => by rw [e]; exact prologue_wp hp) (fun s e => by rw [e]; exact prologue_wp hp')
  have ev {s : State} (h : s.z = decide (N s₀ = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h]
  have ev' {s : State} (h : s.z = decide (N s₀' = 0)) : isa.eval .eq s = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s = _; rw [eval_eq, h, hN]
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧ (LInv s₀' 0 b ∧ b.z = decide (N s₀' = 0))) ∧
      isa.eval .eq a = some true) (Taint.ofRegs []) (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr)
    hnil
  have mid : RelCT isa (fun a b => (LInv s₀ 0 a ∧ a.z = decide (N s₀ = 0)) ∧ (LInv s₀' 0 b ∧ b.z = decide (N s₀' = 0)))
      (.ite .eq (.block []) (.loop body .ne)) (fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev h.1.2, ev' h.2.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv s₀ (N s₀)) (F₂ := LInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ⟨?_, h.1.1.1⟩, ⟨?_, h.1.2.1⟩⟩)
        fun _ _ h => h
      all_goals
        have := h.2; rw [ev h.1.1.2] at this
        have : N s₀ ≠ 0 := by simpa using this
        omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b)
    (Taint.ofRegs [.r10]) (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r10, h.2.r10, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h).seq (mid.seq epi)

theorem update_ct : ConstantTime isa updateArm.pre updateArm.pub update :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.Arm
