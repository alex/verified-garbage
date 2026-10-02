import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateCorrect
import VerifiedGarbage.Proof.Rc2.X86.Cbc.ConstantTime
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# Streaming RC2-CBC on x86 (32-bit): constant time

Untrusted: everything here is checked by Lean. The taint analysis proves
everything but the call of the CBC function (which restores registers the
analysis then takes for secret), from the public arguments on the stack
(`τ0`); the call is related in both runs by `RelCT.callWith`, from what the
correctness proof knows of the state it is made from (`Mid`), and the
restore of our caller's registers through `ebx`, public again by
correctness.
-/

namespace VG.Proof.Rc2.X86.Stream

open VG VG.X86

/-- The arguments on the stack are public, and only read. -/
def τ0 : VG.X86.Taint.T := { regs := .ofList [.esp], flags := false, argLen := 32 }

theorem τ0_wf {s : State} (f : (s.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d : ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r) :
    VG.X86.Taint.Wf τ0 s :=
  Taint.Wf.entry rfl rfl ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨f, fun r hr => Taint.frame_disjoint (n := 28) (by omega) (d r hr).1 (d r hr).2⟩,
    fun _ h => (List.not_mem_nil h).elim⟩

theorem τ0_agree {s₁ s₂ : State} (f₁ : (s₁.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (f₂ : (s₂.gpr .esp).toNat + 32 ≤ 2 ^ 32)
    (d₁ : ∀ r ∈ s₁.wr, Region.Disjoint ⟨(s₁.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₁ 0, 28⟩ r)
    (d₂ : ∀ r ∈ s₂.wr, Region.Disjoint ⟨(s₂.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s₂ 0, 28⟩ r)
    (sp : s₁.gpr .esp = s₂.gpr .esp) (args : ∀ i < 7, arg s₁ i = arg s₂ i) :
    VG.X86.Taint.Agree τ0 s₁ s₂ := by
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, τ0_wf f₁ d₁, τ0_wf f₂ d₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => sp,
    fun k h4 hk => ?_⟩
  · simp only [τ0, RegSet.mem_ofList, List.mem_singleton] at hr
    subst r; exact sp
  · simp only [τ0] at hk
    rw [show Taint.depth τ0.stk = 0 from rfl, Nat.zero_add, Taint.argByte_eq f₁ h4 hk,
      Taint.argByte_eq f₂ h4 hk, Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by decide)),
      Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by decide))]
    exact congrArg _ (args ((k - 4) / 4) (by omega))

namespace Update

open VG.Impl.Rc2.X86.Stream

def Rel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (updateContract d).pre s₁ ∧ (updateContract d).pre s₂ ∧ (updateContract d).pub s₁ s₂

theorem Pre.disj {s : State} (hp : Pre s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r := by
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  exacts [⟨hp.r_c, hp.a_c⟩, ⟨hp.r_o, hp.a_o⟩, ⟨hp.r_s, hp.a_s⟩]

theorem rel_agree {d : Spec.Rc2.Direction} {s₁ s₂ : State} (h : Rel d s₁ s₂) :
    VG.X86.Taint.Agree τ0 s₁ s₂ :=
  τ0_agree (pre_of h.1).sp_fit (pre_of h.2.1).sp_fit (pre_of h.1).disj (pre_of h.2.1).disj h.2.2.1 h.2.2.2

/-- After `head`, in both runs. -/
def MidRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  ∃ σ₁ σ₂, Rel d σ₁ σ₂ ∧ Mid σ₁ s₁ ∧ Mid σ₂ s₂

theorem call_ct (d : Spec.Rc2.Direction) :
    RelCT isa (fun s₁ s₂ => MidRel d s₁ s₂ ∧ isa.eval .e s₁ = some false) (cbcCall d)
      (fun s₁ s₂ => s₁.gpr .ebx = s₂.gpr .ebx) := by
  have ct : RelCT isa (fun s₁ s₂ => MidRel d s₁ s₂ ∧ isa.eval .e s₁ = some false) (cbcCall d)
      (fun _ _ => True) := by
    rintro s₁ s₂ t₁ t₂ u₁ u₂ ⟨⟨σ₁, σ₂, ⟨h₁, h₂, sp, args⟩, m₁, m₂⟩, -⟩ e₁ e₂
    have hp₁ := pre_of h₁
    have hp₂ := pre_of h₂
    obtain ⟨a0, a1, a2, a3, a4⟩ := callEntry_args hp₁ m₁
    obtain ⟨b0, b1, b2, b3, b4⟩ := callEntry_args hp₂ m₂
    have rd : callRd σ₂ s₂ = callRd σ₁ s₁ := by
      simp only [callRd, callEntry_argAddr m₁, callEntry_argAddr m₂, ctx, E, sp, args 0 (by decide)]
    have wr : callWr σ₂ = callWr σ₁ := by
      simp only [callWr, ctx, oA, O, sA, op, scr, args 0 (by decide), args 4 (by decide), args 5 (by decide),
        args 6 (by decide)]
    have ct' : RelCT isa (fun a b => a = s₁ ∧ b = s₂) (cbcCall d) (fun _ _ => True) := by
      rw [cbcCall_eq]
      apply RelCT.callWith (fun s h => Cbc.cbc_body_correct d s h) (Cbc.cbc_constantTime d) (callRd σ₁ s₁)
        (callWr σ₁)
      rintro a b ⟨rfl, rfl⟩
      refine ⟨callPre_ok hp₁ m₁ d, by rw [← rd, ← wr]; exact callPre_ok hp₂ m₂ d, ?_, ?_, ?_⟩
      · rw [m₁.common.esp, m₂.common.esp]; exact sp
      · simp only [State.withRegions_gpr, callEntry_sp m₁, callEntry_sp m₂, E, sp]
      · intro i hi
        simp only [arg_withRegions]
        rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
        · rw [a0, b0, ctx, ctx, args 0 (by decide)]
        · rw [a1, b1, ctx, ctx, args 0 (by decide)]
        · rw [a2, b2, op, op, args 4 (by decide)]
        · rw [a3, b3, O, O, args 5 (by decide)]
        · rw [a4, b4, scr, scr, args 6 (by decide)]
    exact ct' _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  refine (ct.wpDep (F := fun (σ s' : State) => s'.gpr .ebx = σ.gpr .ebx) fun s₁ s₂ h => ?_).mono (fun _ _ h => h) ?_
  · obtain ⟨⟨σ₁, σ₂, ⟨h₁, h₂, -⟩, m₁, m₂⟩, -⟩ := h
    exact ⟨cbcCall_ok (pre_of h₁) m₁ d fun s' _ _ cs _ _ _ => cs .ebx (by simp [calleeSaved]),
      cbcCall_ok (pre_of h₂) m₂ d fun s' _ _ cs _ _ _ => cs .ebx (by simp [calleeSaved])⟩
  · rintro s₁' s₂' ⟨-, s₁, s₂, ⟨⟨σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩, -⟩, e₁, e₂⟩
    rw [e₁, e₂, m₁.ebx, m₂.ebx, scr, scr, args 6 (by decide)]

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (updateContract d).pre (updateContract d).pub (update d) := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold update
  have hA : RelCT isa (Rel d) head (fun _ _ => True) :=
    RelCT.taint (A := taint) τ0 (fun _ _ h => rel_agree h) (by taint_decide)
  refine (hA.wpDep (F := Mid) fun s₁ s₂ (h : Rel d s₁ s₂) => ⟨head_ok (pre_of h.1), head_ok (pre_of h.2.1)⟩).seq
    (RelCT.seq (R := fun (s₁ s₂ : State) => s₁.gpr .ebx = s₂.gpr .ebx) ?_ ?_)
  · apply RelCT.ite
    · rintro s₁ s₂ ⟨-, σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩
      show s₁.zf = s₂.zf
      rw [m₁.zf, m₂.zf, O, O, args 5 (by decide)]
    · apply RelCT.nil
      rintro s₁ s₂ ⟨⟨-, σ₁, σ₂, ⟨-, -, -, args⟩, m₁, m₂⟩, -⟩
      rw [m₁.ebx, m₂.ebx, scr, scr, args 6 (by decide)]
    · exact (call_ct d).mono (fun _ _ h => ⟨h.1.2, h.2⟩) (fun _ _ h => h)
  · exact RelCT.taint (A := taint) (τr [.ebx])
      (fun _ _ h => agree_regs (fun r hr => by rw [List.mem_singleton.mp hr]; exact h)) (by taint_decide)

end Update

end VG.Proof.Rc2.X86.Stream
