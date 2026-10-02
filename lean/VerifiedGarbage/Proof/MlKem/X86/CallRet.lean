import VerifiedGarbage.Proof.MlKem.X86.Piece
import VerifiedGarbage.Impl.MlKem.X86.Basic

/-!
# ML-KEM on x86 (32-bit): calls that return a value

`callWith` pops the frame of a call's arguments into `eax`, where the callee
returns its value; `callRet` pops it into `ecx` instead, and `WP.callRet` also
gives the value in `eax` of the state the callee's postcondition holds of.
-/

namespace VG.X86

open VG.Impl.MlKem.X86 (callRet)

theorem WP.callRet {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) {s : State}
    (hd : 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat) {rd wr : List Region}
    (hk : CallPre k rs rd wr s) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s).callEntry.withRegions rd wr) s₂) → Q s') :
    WP isa (callRet rs n c) s Q := by
  have hn : 4 * rs.length ≤ (s.gpr .esp).toNat := by omega
  have e : ((pushed rs s).gpr .esp).toNat = (s.gpr .esp).toNat - 4 * rs.length := by
    rw [pushed_esp, sub_toNat hn]
  refine WP.frame hne hrs (by decide) hn (fun i hi => hsp i hi) ?_
  refine WP.call hv hsp (by rw [e]; omega) hk.pre (by rw [pushed_rd, pushed_wr]; exact hk.cov)
    (by rw [pushed_wr]; exact hk.covw) fun s₂ rd₂ wr₂ cs₂ f₂ _ ⟨s₃, m₃, g₃, post₃⟩ => ?_
  refine hQ _ (by rw [popped_rd, rd₂, pushed_rd]) (by rw [popped_wr, wr₂, pushed_wr]; rfl) (fun r hr => ?_) ?_
    ⟨s₃, by rw [m₃, popped_mem], by rw [popped_gpr _ _ _ (by decide) (by decide), g₃ _ (by decide)], post₃⟩
  · by_cases h : r = .esp
    · subst h
      rw [popped_esp, cs₂ .esp hr, pushed_esp]; exact BitVec.sub_add_cancel _ _
    · have hne' : r ≠ .ecx := by
        rintro rfl; simp [calleeSaved] at hr
      rw [popped_gpr _ _ _ h hne', cs₂ r hr, pushed_gpr _ _ h]
  · rw [popped_mem]
    refine ((pushed_frame hrs hn).sub fun r hr => ?_).trans (f₂.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), below_sub (by omega) hd⟩
    · rcases List.mem_append.mp hr with hr | hr
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · simp only [List.mem_singleton] at hr; subst hr
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        rw [pushed_esp]
        exact below_inner (by omega) hd

theorem RelCT.callRet {rs : List Reg} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) {P : State → State → Prop} (rd wr : List Region)
    (hP : ∀ s₁ s₂, P s₁ s₂ → CallPre k rs rd wr s₁ ∧ CallPre k rs rd wr s₂ ∧
      s₁.gpr .esp = s₂.gpr .esp ∧
      k.pub ((pushed rs s₁).callEntry.withRegions rd wr) ((pushed rs s₂).callEntry.withRegions rd wr)) :
    RelCT isa P (callRet rs n c) fun _ _ => True := by
  refine RelCT.frame (fun s₁ s₂ h => (hP _ _ h).2.2.1) (RelCT.call hv hct rd wr ?_)
  rintro _ _ ⟨s₁, s₂, h, rfl, rfl⟩
  obtain ⟨k₁, k₂, hsp, hpub⟩ := hP _ _ h
  refine ⟨k₁.pre, k₂.pre, hpub, by rw [pushed_rd, pushed_wr]; exact k₁.cov, by rw [pushed_wr]; exact k₁.covw,
    by rw [pushed_rd, pushed_wr]; exact k₂.cov, by rw [pushed_wr]; exact k₂.covw, ?_⟩
  rw [pushed_esp, pushed_esp, hsp]

end VG.X86

namespace VG.Proof.MlKem.X86.Piece

open VG VG.X86 VG.Impl.MlKem.X86

variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- `Piece.callWith`, for `callRet`. -/
theorem callRet {A B : State → State → Prop} {rs : List Reg} {n : String} {c : Prog isa}
    {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (rd wr : State → List Region)
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat)
    (hk : ∀ s₀ s, Pre s₀ → A s₀ s → CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧ s.gpr .esp = s'.gpr .esp ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧ s₂.gpr .eax = s'.gpr .eax ∧
        k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (callRet rs n c) where
  wp s₀ s h₀ ha := WP.callRet hv hsp hne hrs (hd _ _ h₀ ha) (hk _ _ h₀ ha)
    fun s' h₁ h₂ h₃ h₄ h₅ => hQ _ _ _ h₀ ha h₁ h₂ h₃ h₄ h₅
  ct s₀ s₀' h₀ h₀' hp := RelCT.callRet hv hct (rd s₀) (wr s₀) fun s s' ⟨a, a'⟩ => by
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub _ _ _ _ h₀ h₀' hp a a'
    exact ⟨hk _ _ h₀ a, e₁ ▸ e₂ ▸ hk _ _ h₀' a', e₃, e₄⟩

end VG.Proof.MlKem.X86.Piece
