import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateCall
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.RelCT

/-!
# Poly1305 on x86-64: `update`, constant time and `Verified`

Untrusted: everything here is checked by Lean. `update` calls an
implementation of `vg_poly1305_blocks` that the proof does not know, so the
taint analysis cannot follow it into it. The code before the call
(`updatePre`) and the code after it (`updatePost`) are checked by the taint
analysis; the call is constant time by the implementation's own proof
(`RelCT.callEx`), since its arguments agree in two runs (the analysis of
`updatePre` says so) and correctness says it may access the regions it is
given; and after it, the registers the code after it needs are public again,
since the callee keeps them (`calleeSaved`).
-/

namespace VG.Proof.Poly1305.X86_64

open VG VG.X86_64 VG.Impl.Poly1305.X86_64

/-! ## Constant time -/

/-- The public registers and what is known about memory on entry: the
lengths of the state and `scratch`, and the registers holding their bases. -/
def τ₀ : X86_64.Taint.T :=
  { regs := .ofList [.rdi, .rsi, .rdx, .rcx, .r8, .rsp], flags := false, lens := [128, 128],
    bases := [(.rdi, 0, 0), (.r8, 1, 0)] }

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.updateX86_64.pre s₁)
    (h₂ : Proof.Poly1305.updateX86_64.pre s₂) (hpub : Proof.Poly1305.updateX86_64.pub s₁ s₂) :
    X86_64.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
  have wf : ∀ s, Proof.Poly1305.updateX86_64.pre s → X86_64.Taint.Wf τ₀ s := by
    intro s hs
    obtain ⟨-, hw, d, -⟩ := hs
    refine ⟨fun _ => ⟨by simp [hw, τ₀], by simp [hw, d], by simp [hw]⟩, fun p hp => ?_⟩
    simp only [τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [X86_64.Taint.region, hw]
  refine ⟨⟨fun r hr => ?_, fun h => by cases h⟩, fun _ => ?_, wf _ h₁, wf _ h₂, ?_, ?_,
    X86_64.Taint.noLo⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [h₁.2.1, h₂.2.1, p1, p5]
  · intro sl h; simp [τ₀] at h
  · intro sl h; simp [τ₀] at h

/-- What the code before the call leaves public: the arguments of the call,
what is kept across it, and the flags. -/
abbrev preRegs : List Reg := [.rdi, .rsi, .rdx, .rbx, .rbp, .r12, .r15, .rsp]

/-- What the code after the call needs public: what the call keeps. -/
abbrev postRegs : List Reg := [.rbx, .rbp, .r12, .r15, .rsp]

theorem updatePre_taint : ∃ h, ((taint.check τ₀ updatePre h).map fun τ' =>
    (RegSet.ofList preRegs).subset τ'.regs && τ'.flags) = some true :=
  ⟨_, by taint_decide⟩

theorem updatePost_taint : ∃ h, (taint.check (Taint.ofRegs postRegs) updatePost h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem none_taint : ∃ h, ((taint.check (Taint.ofRegs postRegs) (.block []) h).map fun τ' =>
    (RegSet.ofList postRegs).subset τ'.regs) = some true :=
  ⟨_, by taint_decide⟩

/-- Code the taint analysis proves constant time, which leaves the registers
`rs` and the flags public. -/
theorem RelCT.taintFlags {τ : X86_64.Taint.T} {P : State → State → Prop} {c : Prog isa}
    (hp : ∀ s₁ s₂, P s₁ s₂ → X86_64.Taint.Agree τ s₁ s₂) (rs : List Reg) {hc : VG.Taint.Hint X86_64.Taint.T}
    (h : ((taint.check τ c hc).map fun τ' => (RegSet.ofList rs).subset τ'.regs && τ'.flags) = some true) :
    RelCT isa P c fun s₁ s₂ => (∀ r ∈ rs, s₁.gpr r = s₂.gpr r) ∧ s₁.cf = s₂.cf := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc', hs⟩ := Option.map_eq_some_iff.mp h
  simp only [Bool.and_eq_true] at hs
  obtain ⟨ht, ha⟩ := VG.Taint.check_sound hc' (hp _ _ hP) e₁ e₂
  exact ⟨ht, fun r hr => ha.rf.1 r (RegSet.mem_of_subset hs.1 (RegSet.mem_ofList.mpr hr)), (ha.rf.2 hs.2).1⟩

section
variable (v : BlocksImpl) {s₀ s₀' : State} (h₀ : Proof.Poly1305.updateX86_64.pre s₀)
  (h₀' : Proof.Poly1305.updateX86_64.pre s₀') (hq : Proof.Poly1305.updateX86_64.pub s₀ s₀')
include h₀ h₀' hq

/-- Before the call, in two runs. -/
def Mid (s₀ s₀' : State) (s₁ s₂ : State) : Prop :=
  ((∀ r ∈ preRegs, s₁.gpr r = s₂.gpr r) ∧ s₁.cf = s₂.cf) ∧ (∃ c, Ready s₀ c s₁) ∧ (∃ c, Ready s₀' c s₂)

omit hq in
/-- The call, or none. -/
theorem mid_rel : RelCT isa (Mid s₀ s₀') (.ite .b (.block []) (.call v.name v.code))
    fun s₁ s₂ => ∀ r ∈ postRegs, s₁.gpr r = s₂.gpr r := by
  have hp := UPre.of _ h₀
  have hp' := UPre.of _ h₀'
  have sub : ∀ r ∈ postRegs, r ∈ preRegs := by decide
  refine RelCT.ite (fun s₁ s₂ h => by simp only [eval, h.1.2]) ?_ ?_
  · obtain ⟨_, hn⟩ := none_taint
    exact RelCT.taintRegs (fun s₁ s₂ h => Taint.agree_ofRegs fun r hr => h.1.1.1 r (sub r hr)) postRegs hn
  · have ct := RelCT.callEx (n := v.name) (k := blocksStack v.stack)
      (P := fun s₁ s₂ => Mid s₀ s₀' s₁ s₂ ∧ eval .b s₁ = some false) v.ok v.ct
      fun s₁ s₂ ⟨⟨⟨hr, _⟩, ⟨c₁, r₁⟩, ⟨c₂, r₂⟩⟩, _⟩ => by
        obtain ⟨p₁, cv₁, w₁⟩ := call_pre v hp r₁
        obtain ⟨p₂, cv₂, w₂⟩ := call_pre v hp' r₂
        refine ⟨_, _, _, _, p₁, p₂, ?_, cv₁, w₁, cv₂, w₂, hr .rsp (by simp)⟩
        simp only [blocksStack, Proof.Poly1305.blocksX86_64, State.withRegions_gpr, State.callEntry_rsp,
          State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
          State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp)]
        exact ⟨⟨hr .rdi (by simp), hr .rsi (by simp), hr .rdx (by simp)⟩, by rw [hr .rsp (by simp)]⟩
    have keep : ∀ {σ₀ s : State}, UPre σ₀ → (∃ c, Ready σ₀ c s) → eval .b s = some false →
        WP isa (.call v.name v.code) s fun s' => ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r := by
      intro σ₀ s hp ⟨c, h⟩ he
      rw [eval, h.cf] at he
      simp only [Option.some.injEq, decide_eq_false_iff_not, Nat.not_lt] at he
      exact WP.mono (call_ok v hp h he) fun _ h' => h'.2.1
    refine (ct.wpDep (F := fun (σ s' : State) => ∀ r ∈ calleeSaved, s'.gpr r = σ.gpr r) fun s₁ s₂ h =>
      ⟨keep hp h.1.2.1 h.2, keep hp' h.1.2.2 (by simp only [eval] at h ⊢; rw [← h.1.1.2]; exact h.2)⟩).mono
      (fun _ _ h => h) ?_
    rintro s₁' s₂' ⟨_, σ₁, σ₂, ⟨⟨⟨hr, _⟩, _⟩, _⟩, k₁, k₂⟩ r hr'
    have hc : r ∈ calleeSaved := by
      simp only [postRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]
    rw [k₁ r hc, k₂ r hc, hr r (sub r hr')]

theorem update_rel :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') (update v.name v.code) fun _ _ => True := by
  have hp := UPre.of _ h₀
  have hp' := UPre.of _ h₀'
  obtain ⟨_, hpre⟩ := updatePre_taint
  obtain ⟨_, hpost⟩ := updatePost_taint
  have pre := ((RelCT.taintFlags (P := fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀')
    (fun _ _ h => h.1 ▸ h.2 ▸ agree₀ h₀ h₀' hq) preRegs hpre).wp
    (F₁ := fun s => ∃ c, Ready s₀ c s) (F₂ := fun s => ∃ c, Ready s₀' c s) fun _ _ h =>
      ⟨by rw [h.1]; exact updatePre_ok hp, by rw [h.2]; exact updatePre_ok hp'⟩)
  have post := RelCT.taint (A := taint) (P := fun s₁ s₂ => ∀ r ∈ postRegs, s₁.gpr r = s₂.gpr r)
    (Taint.ofRegs postRegs) (fun _ _ h => Taint.agree_ofRegs h) hpost
  exact pre.seq ((mid_rel v h₀ h₀').seq post)

end

theorem update_ct (v : BlocksImpl) :
    ConstantTime isa Proof.Poly1305.updateX86_64.pre Proof.Poly1305.updateX86_64.pub (update v.name v.code) :=
  fun _ _ _ _ _ _ h₁ h₂ hq e₁ e₂ => (update_rel v h₁ h₂ hq _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-! ## `Verified` -/

/-- A state satisfying the precondition (with no data). -/
def updateSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rdx => 0x2000 | .rsp => 0x4000 | .r8 => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x5000, 128⟩]

theorem update_verified (v : BlocksImpl) :
    Verified X86_64.target (update v.name v.code) (Spec.Poly1305.updateContract X86_64.abi 24) :=
  Verified.of_correct (update_ok v) (update_ct v)
    { pre := by
        sig_implies_pre [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Proof.Poly1305.updateX86_64, X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_eval [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, X86_64.abi, X86_64.argRegs]
        intro key msg hb hc
        exact h key msg hb (count_mod hc)
      pub := by
        sig_implies_pub [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig,
          Proof.Poly1305.updateX86_64, X86_64.abi, X86_64.argRegs]
      sat := by
        sig_implies_sat [Spec.Poly1305.updateContract, Spec.Poly1305.updateSig, X86_64.abi,
          X86_64.argRegs, Proof.Poly1305.X86_64.updateSat]
          [Proof.Poly1305.X86_64.updateSat] using Proof.Poly1305.X86_64.updateSat }

/-- `update` never writes the stack pointer. -/
theorem update_spSafe (v : BlocksImpl) :
    (update v.name v.code).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [update, Code.all, v.spSafe, Bool.and_true]
  lit_decide

end VG.Proof.Poly1305.X86_64
