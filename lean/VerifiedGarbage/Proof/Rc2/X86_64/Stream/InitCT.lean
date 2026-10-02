import VerifiedGarbage.Proof.Rc2.X86_64.Stream.Init
import VerifiedGarbage.Proof.Rc2.X86_64.Stream.UpdateCT

/-! # Streaming RC2-CBC on x86-64: `vg_rc2_cbc_init` is constant time

The length checks and the IV copy are checked by the taint analysis from the
public arguments; the call of key expansion is constant time by its proof,
with the arguments that correctness fixes (`KeyPre`). -/

namespace VG.Proof.Rc2.X86_64.Stream

open VG VG.X86_64 VG.Impl.Rc2.X86_64 VG.Impl.Rc2.X86_64.Stream

def InitRelI (s₁ s₂ : State) : Prop := initContract.pre s₁ ∧ initContract.pre s₂ ∧ initContract.pub s₁ s₂

/-- After the checks, from related entry states. -/
def ChecksRel (σ₁ σ₂ s₁ s₂ : State) : Prop :=
  InitRelI σ₁ σ₂ ∧ Keep [.rax, .r10] σ₁ s₁ ∧ Keep [.rax, .r10] σ₂ s₂ ∧
    s₁.zf = some (decide (code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat = 0)) ∧
    s₂.zf = some (decide (code (σ₂.gpr .rsi).toNat (σ₂.gpr .rdx).toNat (σ₂.gpr .r8).toNat = 0))

theorem checksRel_args {σ₁ σ₂ s₁ s₂ : State} (h : ChecksRel σ₁ σ₂ s₁ s₂) : ∀ r ∈ args, s₁.gpr r = s₂.gpr r := by
  intro r hr
  have hr' : r ∉ [Reg.rax, .r10] := by revert hr; revert r; decide
  rw [h.2.1.reg r hr', h.2.2.1.reg r hr']
  exact h.1.2.2.1 r hr

theorem init_constantTime : ConstantTime isa initContract.pre initContract.pub init := by
  apply RelCT.constantTime (Q := fun _ _ => True)
  have chk : RelCT isa InitRelI checks (fun s₁ s₂ => ∃ σ₁ σ₂, ChecksRel σ₁ σ₂ s₁ s₂) := by
    have ct := RelCT.taint (P := InitRelI) (A := taint) (Taint.ofRegs args)
      (fun _ _ h => Taint.agree_ofRegs h.2.2.1) (c := checks) (by taint_decide)
    refine (ct.wpDep (fun s₁ s₂ _ => ⟨checks_ok s₁, checks_ok s₂⟩)).mono (fun _ _ h => h) ?_
    rintro s₁ s₂ ⟨-, σ₁, σ₂, hp, ⟨k₁, z₁, -⟩, ⟨k₂, z₂, -⟩⟩
    exact ⟨σ₁, σ₂, hp, k₁, k₂, z₁, z₂⟩
  change RelCT isa InitRelI (.seq checks (.ite .ne (.block []) (.seq (.block initArgs)
    (.seq keyCall (.block [.mov32 .rax (.imm 0)]))))) (fun _ _ => True)
  refine chk.seq (RelCT.exists_ fun σ₁ => RelCT.exists_ fun σ₂ => ?_)
  by_cases hI : InitRelI σ₁ σ₂
  swap
  · exact RelCT.of_false fun _ _ h => hI h.1
  obtain ⟨hp₁, hp₂, hpub, hB⟩ := hI
  have hcode : code (σ₂.gpr .rsi).toNat (σ₂.gpr .rdx).toNat (σ₂.gpr .r8).toNat =
      code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat := by
    rw [hpub .rsi (by decide), hpub .rdx (by decide), hpub .r8 (by decide)]
  refine RelCT.ite (fun s₁ s₂ h => ?_) (RelCT.block_nil fun _ _ _ => trivial) ?_
  · simp only [eval, h.2.2.2.1, h.2.2.2.2, hcode]
  by_cases hz : code (σ₁.gpr .rsi).toNat (σ₁.gpr .rdx).toNat (σ₁.gpr .r8).toNat = 0
  swap
  · refine RelCT.of_false fun s₁ s₂ h => ?_
    have e := h.2; simp only [eval, h.1.2.2.2.1, hz] at e; simp at e
  have hv₁ := valid_of_code hz
  have hv₂ := valid_of_code (σ := σ₂) (by rw [hcode]; exact hz)
  have pre := (RelCT.taint (A := taint) (Taint.ofRegs args)
    (P := fun s₁ s₂ => ChecksRel σ₁ σ₂ s₁ s₂ ∧ isa.eval .ne s₁ = some false)
    (fun _ _ h => Taint.agree_ofRegs (checksRel_args h.1)) (c := .block initArgs)
    (by taint_decide)).wp (F₁ := KeyPre σ₁) (F₂ := KeyPre σ₂) fun s₁ s₂ h =>
      ⟨initArgs_pre σ₁ hp₁ hv₁ s₁ h.1.2.1, initArgs_pre σ₂ hp₂ hv₂ s₂ h.1.2.2.1⟩
  refine RelCT.seq pre (RelCT.seq (R := fun _ _ => True) ?_ (RelCT.taint (A := taint) (Taint.ofRegs [])
    (P := fun _ _ => True) (fun _ _ _ => Taint.agree_ofRegs (by simp)) (by taint_decide)))
  have hrd : keyRd σ₂ = keyRd σ₁ := by simp only [keyRd, hpub .rdi (by decide), hpub .rsi (by decide)]
  have hwr : keyWr σ₂ = keyWr σ₁ := by simp only [keyWr, hpub .r9 (by decide), hB]
  refine RelCT.call key_correct (expandKey_constantTime _) (keyRd σ₁) (keyWr σ₁) ?_
  rintro s₁ s₂ ⟨-, m₁, m₂⟩
  obtain ⟨pre₁, c₁, w₁⟩ := key_pre σ₁ hp₁ hv₁ s₁ m₁
  obtain ⟨pre₂, c₂, w₂⟩ := key_pre σ₂ hp₂ hv₂ s₂ m₂
  rw [hrd, hwr] at pre₂ c₂
  rw [hwr] at w₂
  refine ⟨pre₁, pre₂, ?_, c₁, w₁, c₂, w₂, by rw [m₁.rsp, m₂.rsp, hpub .rsp (by decide)]⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [State.withRegions_gpr, State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp),
      State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.r8 ≠ .rsp),
      m₁.rdi, m₂.rdi, m₁.rsi, m₂.rsi, m₁.rdx, m₂.rdx, m₁.rcx, m₂.rcx, m₁.r8, m₂.r8,
      hpub .rdi (by decide), hpub .rsi (by decide), hpub .rdx (by decide), hpub .r9 (by decide), hB]

end VG.Proof.Rc2.X86_64.Stream
