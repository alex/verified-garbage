import VerifiedGarbage.Proof.Rc2.X86.Stream.InitCorrect
import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateCT
import VerifiedGarbage.Proof.Rc2.X86.Key
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# Streaming RC2-CBC on x86 (32-bit): `init` is constant time

Untrusted: everything here is checked by Lean. As for the updates
(`UpdateCT.lean`): the taint analysis proves the checks and the copy of the
IV, `RelCT.callWith` the call of the key expansion, and the restore of our
caller's registers through `ebx`, public again by correctness.
-/

namespace VG.Proof.Rc2.X86.Stream.Init

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

def Rel (s₁ s₂ : State) : Prop := initContract.pre s₁ ∧ initContract.pre s₂ ∧ initContract.pub s₁ s₂

theorem Pre.disj {s₀ s : State} (hp : Pre s₀) (hc : Common s₀ s) :
    ∀ r ∈ s.wr, Region.Disjoint ⟨(s.gpr .esp).setWidth 64, 4⟩ r ∧ Region.Disjoint ⟨argAddr s 0, 28⟩ r := by
  have e : argAddr s 0 = argAddr s₀ 0 := by unfold argAddr; rw [hc.esp]
  rw [hc.wr, hp.wr, hc.esp, e]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  exacts [⟨hp.r_c, hp.a_c⟩, ⟨hp.r_s, hp.a_s⟩]

/-- The arguments, from a state whose memory is the entry state's. -/
theorem arg_eq {s₀ s : State} (hc : Common s₀ s) (hm : s.mem = s₀.mem) (i : Nat) : arg s i = arg s₀ i := by
  unfold arg argAddr; rw [hc.esp, hm]

theorem agree_mid {σ₁ σ₂ s₁ s₂ : State} (h : Rel σ₁ σ₂) (c₁ : Common σ₁ s₁) (c₂ : Common σ₂ s₂)
    (m₁ : s₁.mem = σ₁.mem) (m₂ : s₂.mem = σ₂.mem) : VG.X86.Taint.Agree τ0 s₁ s₂ := by
  have hp₁ := pre_of h.1
  have hp₂ := pre_of h.2.1
  refine τ0_agree (by rw [c₁.esp]; exact hp₁.sp_fit) (by rw [c₂.esp]; exact hp₂.sp_fit) (hp₁.disj c₁)
    (hp₂.disj c₂) (by rw [c₁.esp, c₂.esp]; exact h.2.2.1) fun i hi => ?_
  rw [arg_eq c₁ m₁, arg_eq c₂ m₂]; exact h.2.2.2 i hi

theorem code_eq {σ₁ σ₂ : State} (args : ∀ i < 7, arg σ₁ i = arg σ₂ i) : code σ₁ = code σ₂ := by
  simp only [code, kl, eb, il, args 1 (by decide), args 2 (by decide), args 4 (by decide)]

/-- After the checks and the test of their result. -/
structure Checked (s₀ s : State) : Prop where
  common : Common s₀ s
  mem : s.mem = s₀.mem
  zf : s.zf = some (decide (code s₀ = 0))
  ebx : s.gpr .ebx = s₀.gpr .ebx
  esi : s.gpr .esi = s₀.gpr .esi

theorem checked_ok {s₀ : State} (hp : Pre s₀) :
    WP isa (.seq checks (.block [.alu .test .eax (.reg .eax)])) s₀ (Checked s₀) := by
  refine WP.seq (checks_ok hp fun s c m a b e => wp_test fun s₁ f₁ hz => WP.block_nil ?_)
  refine ⟨c.fupd f₁, by rw [f₁.mem, m], ?_, by rw [f₁.gpr]; exact b, by rw [f₁.gpr]; exact e⟩
  rw [hz, a, BitVec.and_self, ofNat_beq_zero (by have := code_lt s₀; omega)]

/-- Before the call. -/
structure Args (s₀ s : State) : Prop where
  common : Common s₀ s
  eax : s.gpr .eax = key s₀
  ecx : s.gpr .ecx = arg s₀ 1
  edx : s.gpr .edx = arg s₀ 2
  esi : s.gpr .esi = ctx s₀
  ebx : s.gpr .ebx = scr s₀

def CheckedRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, Rel σ₁ σ₂ ∧ Checked σ₁ s₁ ∧ Checked σ₂ s₂

def ArgsRel (s₁ s₂ : State) : Prop := ∃ σ₁ σ₂, Rel σ₁ σ₂ ∧ code σ₁ = 0 ∧ Args σ₁ s₁ ∧ Args σ₂ s₂

theorem args_ct :
    RelCT isa (fun s₁ s₂ => CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs) ArgsRel := by
  have ct : RelCT isa (fun s₁ s₂ => CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) (.block initArgs)
      (fun _ _ => True) := by
    refine RelCT.taint (A := taint) τ0 (fun s₁ s₂ h => ?_) (by taint_decide)
    obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, -⟩ := h
    exact agree_mid hσ k₁.common k₂.common k₁.mem k₂.mem
  have code0 : ∀ {σ s : State}, Checked σ s → isa.eval .ne s = some false → code σ = 0 := fun k z => by
    have : isa.eval .ne _ = _ := congrArg (Option.map (!·)) k.zf
    rw [z] at this
    exact of_decide_eq_true (by revert this; cases decide (code _ = 0) <;> simp)
  have h : ∀ σ : State × State, RelCT isa (fun s₁ s₂ =>
      (CheckedRel s₁ s₂ ∧ isa.eval .ne s₁ = some false) ∧ Rel σ.1 σ.2 ∧ Checked σ.1 s₁ ∧ Checked σ.2 s₂ ∧
        code σ.1 = 0) (.block initArgs) ArgsRel := fun σ => by
    refine ((ct.mono (fun _ _ h => h.1) (fun _ _ h => h)).wp
      (F₁ := fun (s : State) => Rel σ.1 σ.2 ∧ code σ.1 = 0 ∧ Args σ.1 s) (F₂ := Args σ.2) fun s₁ s₂ h => ?_).mono
      (fun _ _ h => h) fun _ _ h => ⟨σ.1, σ.2, h.2.1.1, h.2.1.2.1, h.2.1.2.2, h.2.2⟩
    obtain ⟨-, hσ, k₁, k₂, h0⟩ := h
    have hp₁ := pre_of hσ.1
    have hp₂ := pre_of hσ.2.1
    have h0' : code σ.2 = 0 := (code_eq hσ.2.2.2).symm.trans h0
    exact ⟨initArgs_ok hp₁ (code_ok h0).2.2 k₁.common k₁.mem k₁.ebx k₁.esi
        fun t c ea ec ed es eb _ _ _ => ⟨hσ, h0, c, ea, ec, ed, es, eb⟩,
      initArgs_ok hp₂ (code_ok h0').2.2 k₂.common k₂.mem k₂.ebx k₂.esi
        fun t c ea ec ed es eb _ _ _ => ⟨c, ea, ec, ed, es, eb⟩⟩
  refine (RelCT.exists_ h).mono (fun s₁ s₂ hh => ?_) (fun _ _ h => h)
  obtain ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩ := hh
  exact ⟨(σ₁, σ₂), ⟨⟨σ₁, σ₂, hσ, k₁, k₂⟩, z⟩, hσ, k₁, k₂, code0 k₁ z⟩

theorem call_ct : RelCT isa ArgsRel keyCall (fun s₁ s₂ => s₁.gpr .ebx = s₂.gpr .ebx) := by
  rintro s₁ s₂ t₁ t₂ u₁ u₂ ⟨σ₁, σ₂, ⟨h₁, h₂, sp, args⟩, h0, a₁, a₂⟩ e₁ e₂
  have hp₁ := pre_of h₁
  have hp₂ := pre_of h₂
  have h0' : code σ₂ = 0 := (code_eq args).symm.trans h0
  obtain ⟨hk₁, he₁, -⟩ := code_ok h0
  obtain ⟨hk₂, he₂, -⟩ := code_ok h0'
  have pre₁ := keyCallPre_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
  have pre₂ := keyCallPre_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
  have fit (s : State) (σ : State) (hp : Pre σ) (c : Common σ s) : 4 * rs5.length + 4 ≤ (s.gpr .esp).toNat := by
    rw [c.esp]; simp only [List.length_cons, List.length_nil]; have := hp.sp_lo; omega
  have hrs : Reg.esp ∉ rs5 := by decide
  have esp : s₁.gpr .esp = s₂.gpr .esp := by rw [a₁.common.esp, a₂.common.esp]; exact sp
  have rd : callRd σ₂ s₂ = callRd σ₁ s₁ := by
    simp only [callRd, callEntry_argAddr0, esp, keyR, kA, kl, key, args 0 (by decide), args 1 (by decide)]
  have wr : callWr σ₂ = callWr σ₁ := by
    simp only [callWr, schR, cA, sA, ctx, scr, args 5 (by decide), args 6 (by decide)]
  have ct : RelCT isa (fun a b => a = s₁ ∧ b = s₂) keyCall (fun _ _ => True) := by
    apply RelCT.callWith key_body_correct expandKey_constantTime (callRd σ₁ s₁) (callWr σ₁)
    intro a b hab
    rw [hab.1, hab.2]
    refine ⟨pre₁, by rw [← rd, ← wr]; exact pre₂, esp, ?_, ?_⟩
    · simp only [State.withRegions_gpr, callEntry_esp', esp]
    · intro i hi
      simp only [arg_withRegions]
      rw [callEntry_arg (fit _ _ hp₁ a₁.common) hrs (by simpa using hi),
        callEntry_arg (fit _ _ hp₂ a₂.common) hrs (by simpa using hi)]
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl
      · show s₁.gpr .eax = s₂.gpr .eax; rw [a₁.eax, a₂.eax, key, key, args 0 (by decide)]
      · show s₁.gpr .ecx = s₂.gpr .ecx; rw [a₁.ecx, a₂.ecx, args 1 (by decide)]
      · show s₁.gpr .edx = s₂.gpr .edx; rw [a₁.edx, a₂.edx, args 2 (by decide)]
      · show s₁.gpr .esi = s₂.gpr .esi; rw [a₁.esi, a₂.esi, ctx, ctx, args 5 (by decide)]
      · show s₁.gpr .ebx = s₂.gpr .ebx; rw [a₁.ebx, a₂.ebx, scr, scr, args 6 (by decide)]
  obtain ⟨ht, -, b₁, b₂⟩ := (ct.wp (F₁ := fun (s : State) => s.gpr .ebx = scr σ₁) (F₂ := fun (s : State) => s.gpr .ebx = scr σ₂)
    fun a b ⟨ha, hb⟩ => by
      subst ha hb
      exact ⟨keyCall_ok hp₁ hk₁ he₁ a₁.common a₁.eax a₁.ecx a₁.edx a₁.esi a₁.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₁.ebx,
        keyCall_ok hp₂ hk₂ he₂ a₂.common a₂.eax a₂.ecx a₂.edx a₂.esi a₂.ebx
          fun s' _ _ cs _ _ => (cs .ebx (by simp [calleeSaved])).trans a₂.ebx⟩) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂
  exact ⟨ht, show u₁.gpr .ebx = u₂.gpr .ebx by rw [b₁, b₂, scr, scr, args 6 (by decide)]⟩

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  unfold init
  apply RelCT.assoc
  have hA : RelCT isa Rel (.seq checks (.block [.alu .test .eax (.reg .eax)])) (fun _ _ => True) :=
    RelCT.taint (A := taint) τ0 (fun s₁ s₂ h => agree_mid h (Common.refl _) (Common.refl _) rfl rfl)
      (by taint_decide)
  refine ((hA.wpDep (F := Checked) fun s₁ s₂ (h : Rel s₁ s₂) =>
    ⟨checked_ok (pre_of h.1), checked_ok (pre_of h.2.1)⟩).mono (fun _ _ h => h)
      (Q' := CheckedRel) fun _ _ h => h.2).seq ?_
  apply RelCT.ite
  · rintro s₁ s₂ ⟨σ₁, σ₂, ⟨-, -, -, args⟩, k₁, k₂⟩
    show s₁.zf.map (!·) = s₂.zf.map (!·)
    rw [k₁.zf, k₂.zf, code_eq args]
  · exact RelCT.nil fun _ _ _ => trivial
  · unfold initBody
    refine args_ct.seq (call_ct.seq ?_)
    exact RelCT.taint (A := taint) (τr [.ebx])
      (fun _ _ h => agree_regs (fun r hr => by rw [List.mem_singleton.mp hr]; exact h)) (by taint_decide)

end VG.Proof.Rc2.X86.Stream.Init
