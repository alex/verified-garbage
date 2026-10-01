import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
import VerifiedGarbage.Proof.Framework.X86_64.Taint

/-!
# AES-CMAC on x86-64: `vg_cmac_aes_update` is constant time

Untrusted: everything here is checked by Lean. Two runs from states that
agree on the public arguments are related piece by piece (`RelCT`): the
taint analysis covers the code between the calls, from the registers the
correctness proof pins to the public arguments (`LInv`), and each call of
`vg_aes_ctr32` is constant time by its own proof (`ctr_rel`).
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64 VG.Impl.CmacAes.X86_64
open VG.Proof.Aes.X86_64 (Ctr32Impl)

section
variable {s₀ s₀' : State} (hq : updateX86_64.pub s₀ s₀')
include hq

theorem pub_W : W s₀ = W s₀' := hq.1
theorem pub_rsi : s₀.gpr .rsi = s₀'.gpr .rsi := hq.2.1
theorem pub_R : R s₀ = R s₀' := by rw [R, R, pub_rsi hq]
theorem pub_St : St s₀ = St s₀' := hq.2.2.1
theorem pub_Dp : Dp s₀ = Dp s₀' := hq.2.2.2.1
theorem pub_N : N s₀ = N s₀' := by rw [N, N, hq.2.2.2.2.1]
theorem pub_S : S s₀ = S s₀' := hq.2.2.2.2.2.1
theorem pub_rsp : s₀.gpr .rsp = s₀'.gpr .rsp := hq.2.2.2.2.2.2

/-- The registers the invariant pins agree in both runs. -/
theorem LInv.agree {k : Nat} {s₁ s₂ : State} (h₁ : LInv s₀ k s₁) (h₂ : LInv s₀' k s₂) :
    ∀ r ∈ [Reg.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.rbx, h₂.rbx, pub_W hq]
  · rw [h₁.rbp, h₂.rbp, pub_rsi hq]
  · rw [h₁.r12, h₂.r12, pub_St hq]
  · rw [h₁.r13, h₂.r13, pub_Dp hq]
  · rw [h₁.r14, h₂.r14, pub_N hq]
  · rw [h₁.r15, h₂.r15, pub_S hq]
  · rw [h₁.rsp, h₂.rsp, pub_rsp hq]

end

/-! ## One block -/

/-- What is known between the code before the call and the call. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  pre : CallPre s (W s₀) (S s₀ + BitVec.ofNat 64 2048) (St s₀) (S s₀) (R s₀)
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)
  rsp : s.gpr .rsp = s₀.gpr .rsp

theorem bodyMid_wp {s₀ : State} (hp : UPre s₀) {k : Nat} (hk : k < N s₀) {s : State} (h : LInv s₀ k s) :
    WP isa (.block (chainIn ++ updArgs)) s (Mid s₀ k) :=
  WP.mono (bodyA_wp hp hk h) fun _ hb =>
    ⟨hb.pre, by rw [hb.saved .r13 (by simp [calleeSaved]), h.r13],
      by rw [hb.saved .r14 (by simp [calleeSaved]), h.r14], by rw [hb.saved .rsp (by simp [calleeSaved]), h.rsp]⟩

/-- What is known after the call. -/
structure After (s₀ : State) (k : Nat) (s : State) : Prop where
  r13 : s.gpr .r13 = Dp s₀ + BitVec.ofNat 64 (16 * k)
  r14 : s.gpr .r14 = BitVec.ofNat 64 (N s₀ - k)

theorem body_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateX86_64.pub s₀ s₀') (k : Nat) :
    RelCT isa (fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) (body v.callee) fun _ _ => True := by
  obtain ⟨_, hA⟩ : ∃ h, (taint.check (Taint.ofRegs [.rbx, .rbp, .r12, .r13, .r14, .r15, .rsp])
      (.block (chainIn ++ updArgs)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hB⟩ : ∃ h, (taint.check (Taint.ofRegs [.r13, .r14]) (.block advance) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have a := (RelCT.taint (A := taint) (P := fun s₁ s₂ => k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂) _
    (fun _ _ h => Taint.agree_ofRegs (LInv.agree hq h.2.1 h.2.2)) hA).wp
    (F₁ := Mid s₀ k) (F₂ := Mid s₀' k) fun _ _ h =>
      ⟨bodyMid_wp hp h.1 h.2.1, bodyMid_wp hp' (by rw [← pub_N hq]; exact h.1) h.2.2⟩
  have c := (ctr_rel v (P := fun s₁ s₂ => Mid s₀ k s₁ ∧ Mid s₀' k s₂) fun s₁ s₂ h =>
      ⟨_, _, _, _, _, h.1.pre, by
        rw [pub_W hq, pub_S hq, pub_St hq, pub_R hq]; exact h.2.pre,
        by rw [h.1.rsp, h.2.rsp, pub_rsp hq]⟩).wp
    (F₁ := After s₀ k) (F₂ := After s₀' k) fun s₁ s₂ h =>
      ⟨WP.mono (ctr_call v h.1.pre) fun _ hc =>
        ⟨by rw [hc.saved .r13 (by simp [calleeSaved]), h.1.r13],
          by rw [hc.saved .r14 (by simp [calleeSaved]), h.1.r14]⟩,
       WP.mono (ctr_call v h.2.pre) fun _ hc =>
        ⟨by rw [hc.saved .r13 (by simp [calleeSaved]), h.2.r13],
          by rw [hc.saved .r14 (by simp [calleeSaved]), h.2.r14]⟩⟩
  have b := RelCT.taint (A := taint) (P := fun s₁ s₂ => After s₀ k s₁ ∧ After s₀' k s₂) _
    (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.1.r13, h.2.r13, pub_Dp hq]
      · rw [h.1.r14, h.2.r14, pub_N hq]) hB
  exact (a.mono (fun _ _ h => h) fun _ _ h => h.2).seq
    ((c.mono (fun _ _ h => h) fun _ _ h => h.2).seq b)

/-! ## The loop -/

/-- The loop's relation, with the number of iterations left. -/
def LRel (s₀ s₀' : State) (n : Nat) (s₁ s₂ : State) : Prop :=
  ∃ k, n = N s₀ - k ∧ k < N s₀ ∧ LInv s₀ k s₁ ∧ LInv s₀' k s₂

theorem loop_ct (v : Ctr32Impl) {s₀ s₀' : State} (hp : UPre s₀) (hp' : UPre s₀')
    (hq : updateX86_64.pub s₀ s₀') (n : Nat) :
    RelCT isa (LRel s₀ s₀' n) (.loop (body v.callee) .ne)
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
    (F₁ := fun (s' : State) => LInv s₀ (k + 1) s' ∧ s'.zf = some (decide (N s₀ - (k + 1) = 0)))
    (F₂ := fun (s' : State) => LInv s₀' (k + 1) s' ∧ s'.zf = some (decide (N s₀' - (k + 1) = 0)))
    fun _ _ h => ⟨body_ok v hp h.1 h.2.1, body_ok v hp' (by rw [← hN]; exact h.1) h.2.2⟩
  refine ct.mono (fun _ _ h => h.2) fun s₁ s₂ ⟨_, ⟨l₁, z₁⟩, ⟨l₂, z₂⟩⟩ => ?_
  rw [← hN] at z₂
  have e₁ : isa.eval .ne s₁ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₁.zf.map _ = _; rw [z₁]; rfl
  have e₂ : isa.eval .ne s₂ = some (!decide (N s₀ - (k + 1) = 0)) := by
    show s₂.zf.map _ = _; rw [z₂]; rfl
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

theorem update_rel (v : Ctr32Impl) {s₀ s₀' : State} (h0 : updateX86_64.pre s₀) (h0' : updateX86_64.pre s₀')
    (hq : updateX86_64.pub s₀ s₀') :
    RelCT isa (fun a b => a = s₀ ∧ b = s₀') (update v.callee) fun _ _ => True := by
  have hp := UPre.of h0
  have hp' := UPre.of h0'
  have hN := pub_N hq
  obtain ⟨_, hpro⟩ : ∃ h, (taint.check (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp])
      (.block (save ++ setup)) h).isSome = true := ⟨_, by taint_decide⟩
  obtain ⟨_, hepi⟩ : ∃ h, (taint.check (Taint.ofRegs [.r15]) (.block restore) h).isSome = true :=
    ⟨_, by taint_decide⟩
  obtain ⟨_, hnil⟩ : ∃ h, (taint.check (Taint.ofRegs []) (.block []) h).isSome = true :=
    ⟨_, by taint_decide⟩
  have pro := (RelCT.taint (A := taint) (P := fun a b => a = s₀ ∧ b = s₀') _
    (fun a b h => by
      obtain ⟨rfl, rfl⟩ := h
      refine Taint.agree_ofRegs fun r hr => ?_
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption) hpro).wp
    (F₁ := fun (s : State) => LInv s₀ 0 s ∧ s.zf = some (decide (N s₀ = 0)))
    (F₂ := fun (s : State) => LInv s₀' 0 s ∧ s.zf = some (decide (N s₀' = 0)))
    fun a b h => by obtain ⟨rfl, rfl⟩ := h; exact ⟨prologue_wp hp, prologue_wp hp'⟩
  have nil := RelCT.taint (A := taint)
    (P := fun a b => ((LInv s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0)))) ∧ isa.eval .e a = some true) _
    (fun _ _ _ => Taint.agree_ofRegs fun r hr => by simp at hr) hnil
  have mid : RelCT isa (fun a b => (LInv s₀ 0 a ∧ a.zf = some (decide (N s₀ = 0))) ∧
      (LInv s₀' 0 b ∧ b.zf = some (decide (N s₀' = 0))))
      (.ite .e (.block []) (.loop (body v.callee) .ne))
      (fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) := by
    refine RelCT.ite (fun a b h => ?_) ?_ ?_
    · show a.zf = b.zf; rw [h.1.2, h.2.2, hN]
    · refine (nil.wp (F₁ := LInv s₀ (N s₀)) (F₂ := LInv s₀' (N s₀')) fun a b h => ?_).mono
        (fun _ _ h => h) fun _ _ h => h.2
      have h0 : N s₀ = 0 := by
        have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this; simpa using this
      exact ⟨WP.block_nil (h0 ▸ h.1.1.1), WP.block_nil (by rw [← hN, h0]; exact h.1.2.1)⟩
    · refine (loop_ct v hp hp' hq (N s₀ - 0)).mono (fun a b h => ⟨0, rfl, ?_, h.1.1.1, h.1.2.1⟩)
        fun _ _ h => h
      have := h.2; change a.zf = _ at this; rw [h.1.1.2] at this
      have : N s₀ ≠ 0 := by simpa using this
      omega
  have epi := RelCT.taint (A := taint) (P := fun a b => LInv s₀ (N s₀) a ∧ LInv s₀' (N s₀') b) _
    (fun a b h => Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr; rw [h.1.r15, h.2.r15, pub_S hq]) hepi
  exact (pro.mono (fun _ _ h => h) fun _ _ h => h.2).seq (mid.seq epi)

theorem update_ct (v : Ctr32Impl) :
    ConstantTime isa updateX86_64.pre updateX86_64.pub (update v.callee) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.CmacAes.X86_64
