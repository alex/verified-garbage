import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Update
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # Streaming RC2-CBC on x86-64: the update functions are constant time

The taint analysis checks the code before the call of the CBC function from
the public arguments; the call is constant time by the CBC function's proof,
with the arguments that correctness fixes (`Mid`), which are the same in two
runs that agree on the public arguments (the scratch pointer among them,
which the analysis cannot follow through its load from the stack). -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def args : List Reg := [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp]

def InitRel (d : Spec.Rc2.Direction) (s₁ s₂ : State) : Prop :=
  (updateContract d).pre s₁ ∧ (updateContract d).pre s₂ ∧ (updateContract d).pub s₁ s₂

/-- After the test of `out_len`, from related entry states. -/
def TestRel (d : Spec.Rc2.Direction) (σ₁ σ₂ s₁ s₂ : State) : Prop :=
  InitRel d σ₁ σ₂ ∧ Keep [] σ₁ s₁ ∧ Keep [] σ₂ s₂ ∧ s₁.zf = some (decide ((σ₁.gpr .r9).toNat = 0)) ∧
    s₂.zf = some (decide ((σ₂.gpr .r9).toNat = 0))

theorem cbc_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (Cbc.contract d).pre (Cbc.contract d).pub (Cbc.cbc d) := by
  cases d
  · exact Cbc.encrypt_constantTime _
  · exact Cbc.decrypt_constantTime _

theorem testRel_args {d : Spec.Rc2.Direction} {σ₁ σ₂ s₁ s₂ : State} (h : TestRel d σ₁ σ₂ s₁ s₂) :
    ∀ r ∈ args, s₁.gpr r = s₂.gpr r := by
  intro r hr
  rw [h.2.1.reg r (by simp), h.2.2.1.reg r (by simp)]
  exact h.1.2.2.1 r hr

theorem update_constantTime (d : Spec.Rc2.Direction) :
    ConstantTime isa (updateContract d).pre (updateContract d).pub (update d) := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  -- The test of `out_len`.
  have test : RelCT isa (InitRel d) (.block [.alu .test .r9 (.reg .r9)])
      (fun s₁ s₂ => ∃ σ₁ σ₂, TestRel d σ₁ σ₂ s₁ s₂) := by
    have ct := RelCT.taint (P := InitRel d) (A := taint) (Taint.ofRegs args)
      (fun _ _ h => Taint.agree_ofRegs h.2.2.1) (c := .block [.alu .test .r9 (.reg .r9)]) (by taint_decide)
    have hw (s : State) : WP isa (.block [.alu .test .r9 (.reg .r9)]) s
        (fun s' => Keep [] s s' ∧ s'.zf = some (decide ((s.gpr .r9).toNat = 0))) := by
      obtain ⟨s', run, zf, keep⟩ := test_ok s .r9 (toNat_eq _) (s.gpr .r9).isLt
      exact WP.of_runBlock ⟨s', run, keep, zf⟩
    refine (ct.wpDep (F := fun (s s' : State) => Keep [] s s' ∧ s'.zf = some (decide ((s.gpr .r9).toNat = 0)))
      (fun s₁ s₂ _ => ⟨hw s₁, hw s₂⟩)).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨k₁, z₁⟩, ⟨k₂, z₂⟩⟩
    exact ⟨σ₁, σ₂, hp, k₁, k₂, z₁, z₂⟩
  change RelCT isa (InitRel d) (.seq _ (.ite .e short (.seq longPre (cbcCall d)))) (fun _ _ => True)
  refine test.seq (RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_)
  by_cases hI : InitRel d σ₁ σ₂
  swap
  · exact RelCT.of_false fun _ _ h => hI h.1
  obtain ⟨hp₁, hp₂, hpub, hB⟩ := hI
  refine RelCT.ite (fun s₁ s₂ h => ?_) ?_ ?_
  · simp only [eval, h.2.2.2.1, h.2.2.2.2, hpub .r9 (by decide)]
  · -- No complete block: the taint analysis alone.
    exact RelCT.taint (A := taint) (Taint.ofRegs args) (fun _ _ h => Taint.agree_ofRegs (testRel_args h.1))
      (by taint_decide)
  · -- The copies, then the call.
    by_cases hz : (σ₁.gpr .r9).toNat = 0
    · refine RelCT.of_false fun s₁ s₂ h => ?_
      have e := h.2; simp only [eval, h.1.2.2.2.1, hz] at e; simp at e
    have hz₂ : (σ₂.gpr .r9).toNat ≠ 0 := by rw [← hpub .r9 (by decide)]; exact hz
    have pre := (RelCT.taint (A := taint) (Taint.ofRegs args)
      (P := fun s₁ s₂ => TestRel d σ₁ σ₂ s₁ s₂ ∧ isa.eval .e s₁ = some false)
      (fun _ _ h => Taint.agree_ofRegs (testRel_args h.1)) (c := longPre)
      (by taint_decide)).wp (F₁ := Mid σ₁) (F₂ := Mid σ₂) fun s₁ s₂ h =>
        ⟨long_ok d σ₁ hp₁ hz s₁ h.1.2.1, long_ok d σ₂ hp₂ hz₂ s₂ h.1.2.2.1⟩
    refine RelCT.seq pre ?_
    have hrd : callRd σ₂ = callRd σ₁ := by simp only [callRd, hpub .rdi (by decide)]
    have hwr : callWr σ₂ = callWr σ₁ := by
      simp only [callWr, hpub .rdi (by decide), hpub .r8 (by decide), hpub .r9 (by decide), hB]
    rw [cbcCall_eq]
    refine RelCT.call (cbc_correct d) (cbc_constantTime d) (callRd σ₁) (callWr σ₁) ?_
    rintro s₁ s₂ ⟨-, m₁, m₂⟩
    obtain ⟨pre₁, c₁, w₁⟩ := call_pre d σ₁ hp₁ hz s₁ m₁
    obtain ⟨pre₂, c₂, w₂⟩ := call_pre d σ₂ hp₂ hz₂ s₂ m₂
    rw [hrd, hwr] at pre₂ c₂
    rw [hwr] at w₂
    refine ⟨pre₁, pre₂, ?_, c₁, w₁, c₂, w₂, by rw [m₁.rsp, m₂.rsp, hpub .rsp (by decide)]⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [State.withRegions_gpr, State.callEntry_rsp, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
        State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
        m₁.rdi, m₂.rdi, m₁.rsi, m₂.rsi, m₁.rdx, m₂.rdx, m₁.rcx, m₂.rcx, m₁.r8, m₂.r8, m₁.rsp, m₂.rsp,
        hpub .rdi (by decide), hpub .r8 (by decide), hpub .r9 (by decide), hpub .rsp (by decide), hB]

end VG.Proof.Rc2.X86_64.Stream
