import VerifiedGarbage.Proof.CmacAes.AArch64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.AArch64.Taint

/-!
# AES-CMAC on AArch64: `vg_cmac_aes_update` is constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proof pins to the public arguments (`LInv`), and each call of
`vg_aes_ctr32` is constant time by its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.AArch64

open VG VG.AArch64 VG.Impl.CmacAes.AArch64
open VG.Proof.Aes.AArch64 (Ctr32Impl)

/-- States agree on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : VG.AArch64.Taint.Agree (Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

section
variable {s₀ s₀' : State} (hq : updateAArch64.pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_x1 : s₀.gpr .x1 = s₀'.gpr .x1 := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_x1 hq]
theorem pub_St : St s₀ = St s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_sp : s₀.sp = s₀'.sp := hq.2.2.2.2.2.2

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv s₀ k s₁) (h₂ : LInv s₀' k s₂) :
    VG.AArch64.Taint.Agree (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24]) s₁ s₂ := by
  refine agree_of (by rw [h₁.sp, h₂.sp, pub_sp hq]) fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.x19, h₂.x19, pub_W hq]
  · rw [h₁.x20, h₂.x20, pub_x1 hq]
  · rw [h₁.x21, h₂.x21, pub_St hq]
  · rw [h₁.x22, h₂.x22, pub_Dp hq]
  · rw [h₁.x23, h₂.x23, pub_N hq]
  · rw [h₁.x24, h₂.x24, pub_S hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  x22 : s.gpr .x22 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem bodyMid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.saved .x22 (by simp [preserved]), h.x22],
      by rw [hb.saved .x23 (by simp [preserved]), h.x23], by rw [hb.sp, h.sp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  x22 : s.gpr .x22 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  x23 : s.gpr .x23 = BitVec.ofNat 64 (N s₀ - k)
  sp : s.sp = s₀.sp

theorem body_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateAArch64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) (body v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.x19, .x20, .x21, .x22, .x23, .x24])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.x22, .x23]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) _
    (fun _ _ h => LInv.agree hq h.2.1 h.2.2) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨bodyMid_wp hp h.1 h.2.1, bodyMid_wp hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (ctr_rel v (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨h.1.pre, by rw [pub_W hq, pub_S hq, pub_St hq, pub_R hq]; exact h.2.pre,
        by rw [h.1.sp, h.2.sp, pub_sp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.1.x22],
          by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.1.x23], by rw [hc.sp, h.1.sp]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .x22 (by simp [preserved]) (by decide), h.2.x22],
          by rw [hc.saved .x23 (by simp [preserved]) (by decide), h.2.x23], by rw [hc.sp, h.2.sp]⟩⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.x22, h.2.x22, pub_Dp hq]
      · rw [h.1.x23, h.2.x23, pub_N hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂

theorem loop_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateAArch64.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop (body v.callee) (.nonzero .x .x23))
      fun s₁ s₂ => LInv s₀ (N s₀) s₁ ∧ LInv s₀' (N s₀') s₂ := by
  refine RelCT.loop (M := isa) (LRel s₀ s₀') (fun n => ?_) n
  have hN := pub_N hq
  refine (RelCT.exists_ fun k => ?_).mono (fun s₁ s₂ (h : LRel s₀ s₀' n s₁ s₂) => h) fun _ _ h => h
  by_cases hn : n = N s₀ - k
  swap
  · exact RelCT.of_false fun _ _ h => hn h.1
  subst hn
  by_cases hk : k < N s₀
  swap
  · exact RelCT.of_false fun _ _ h => hk h.2.1
  have ct := (body_ct v hp hp' hq k).wp
    (F₁ := LInv s₀ (k + 1)) (F₂ := LInv s₀' (k + 1))
    fun _ _ h => ⟨body_ok v hp h.1 h.2.1, body_ok v hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, l₁, l₂⟩ => ?_
  have hb : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  have e₁ := eval_x23 (x := N s₀ - (k + 1)) (by omega) l₁.x23
  have e₂ := eval_x23 (x := N s₀ - (k + 1)) (by omega) (by rw [l₂.x23, ← hN])
  refine ⟨by rw [e₁, e₂], fun hf => ?_, fun ht => ?_⟩
  · rw [e₁] at hf
    have h0 : N s₀ = k + 1 := by
      have : N s₀ - (k + 1) = 0 := by simpa using hf
      omega
    exact ⟨h0 ▸ l₁, by rw [← hN, h0]; exact l₂⟩
  · rw [e₁] at ht
    have h0 : N s₀ - (k + 1) ≠ 0 := by simpa using ht
    exact ⟨N s₀ - (k + 1), by omega, k + 1, rfl, by omega, l₁, l₂⟩

/-! ## The whole function -/

theorem update_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : updateAArch64.pre s₀)
    (h0' : updateAArch64.pre s₀') (hq : updateAArch64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  have hb : N s₀ < 2 ^ 64 := (s₀.gpr .x4).isLt
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.x0, .x1, .x2, .x3, .x4, .x5])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.x24]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      refine agree_of h7 fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hpro).wp
    (F₁ := LInv s₀ 0) (F₂ := LInv s₀' 0)
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have ev {k : Nat} {s : State} (h : LInv s₀ 0 s) :
      isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hb (by rw [h.x23]; rfl)
  have ev' {s : State} (h : LInv s₀' 0 s) : isa.eval (.zero .x .x23) s = some (decide (N s₀ = 0)) :=
    eval_zero_x23 hb (by rw [h.x23, ← hN]; rfl)
  have nil := RelCT.taint (A := taint)
    (P := fun a b => (LInv s₀ 0 a ∧ LInv s₀' 0 b) ∧ isa.eval (.zero .x .x23) a = some true) _
    (fun a b h => agree_of (by rw [h.1.1.sp, h.1.2.sp, pub_sp hq]) fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => LInv s₀ 0 a ∧ LInv s₀' 0 b)
      (.ite (.zero .x .x23) (.block []) (.loop (body v.callee) (.nonzero .x .x23)))
      (fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => by rw [ev (k := 0) h.1, ev' h.2]) ?_ ?_
    · refine (nil.wp (F₁ := LInv s₀ (N s₀)) (F₂ := LInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; rw [ev (k := 0) h.1.1] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2)⟩
    · refine (loop_ct v hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1, h.1.2⟩)
        fun _ _ h => h
      have := h.2; rw [ev (k := 0) h.1.1] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) _
    (fun a b h => agree_of (by rw [h.1.sp, h.2.sp, pub_sp hq]) fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.x24, h.2.x24, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct (v : Ctr32Impl) :
    ConstantTime isa updateAArch64.pre updateAArch64.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.AArch64
