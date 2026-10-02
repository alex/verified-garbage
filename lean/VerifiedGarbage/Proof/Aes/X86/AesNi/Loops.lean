import VerifiedGarbage.Proof.Aes.X86.AesNi.Tail
import VerifiedGarbage.Proof.Aes.X86.AesNi.Body

namespace VG.Proof.Aes.X86.AesNi
open VG VG.X86
open VG.Proof.Aes.X86 (CPre nBlk)
open VG.Impl.Aes.X86.AesNi (body6 body1)

/-- The six-lane body advances the public loop state by six blocks. -/
theorem body6_ok {s₀ : State} (hp : CPre s₀) {c : Nat} (hc : c + 6 ≤ nBlk s₀)
    {s : State} (hI : Inv s₀ c c s) :
    WP isa Impl.Aes.X86.AesNi.body6 s fun s' =>
      Inv s₀ (c + 6) (c + 6) s' ∧ s'.cf = some (decide (nBlk s₀ - (c + 6) < 6)) := by
  refine blocks_ok hp Impl.Aes.X86.AesNi.regs6 (.inl rfl) _ hc hI fun s₁ hI₁ => ?_
  change WP isa (.block (([.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6)] : List Instr) ++
    ([.alu .cmp .edi (.imm 6)] : List Instr))) s₁ _
  rw [WP.block_append_iff]
  exact WP.mono (advance_ok hp hc hI₁) fun s₂ ⟨hI₂, _⟩ =>
    cmpEdi_ok (by decide) (by omega) hI₂

/-- The tail body advances one block and exposes its public zero flag. -/
theorem body1_ok {s₀ : State} (hp : CPre s₀) {c : Nat} (hc : c < nBlk s₀)
    {s : State} (hI : Inv s₀ c c s) :
    WP isa Impl.Aes.X86.AesNi.body1 s fun s' =>
      Inv s₀ (c + 1) (c + 1) s' ∧ s'.zf = some (decide (nBlk s₀ - (c + 1) = 0)) := by
  refine blocks_ok hp [.xmm0] (.inr rfl) _ hc hI fun s₁ hI₁ => ?_
  exact advance_ok (n := 1) hp (by omega) hI₁


/-- Both public count loops terminate and encrypt every requested block. -/
theorem loops_ok {s₀ : State} (hp : CPre s₀) {s : State} (hI : Inv s₀ 0 0 s)
    (hcf : s.cf = some (decide (nBlk s₀ < 6))) (finish : Prog isa) {Q : State → Prop}
    (hQ : ∀ s', Inv s₀ (nBlk s₀) (nBlk s₀) s' → WP isa finish s' Q) :
    WP isa (.seq (.ite .b (.block []) (.loop body6 .ae))
      (.seq (.block [.alu .test .edi (.reg .edi)])
        (.seq (.ite .e (.block []) (.loop body1 .ne)) finish))) s Q := by
  refine WP.seq (WP.mono (Q := fun s => ∃ c, nBlk s₀ - c < 6 ∧ Inv s₀ c c s) ?_ fun s₂ ⟨c, hc, hI₂⟩ => ?_)
  · refine WP.ite (decide (nBlk s₀ < 6)) (by simp [eval, hcf]) (fun h => ?_) (fun h => ?_)
    · exact WP.block_nil ⟨0, by simpa using h, hI⟩
    · let I6 : Nat → State → Prop := fun m s => ∃ c, m = nBlk s₀ - c ∧ c + 6 ≤ nBlk s₀ ∧ Inv s₀ c c s
      have hstep : ∀ m s, I6 m s → WP isa body6 s (fun s' =>
          (eval .ae s' = some false ∧ ∃ c, nBlk s₀ - c < 6 ∧ Inv s₀ c c s') ∨
          (eval .ae s' = some true ∧ ∃ m' < m, I6 m' s')) := by
        rintro m s ⟨c, rfl, hc, hI⟩
        refine WP.mono (body6_ok hp hc hI) fun s' ⟨hI', hcf'⟩ => ?_
        by_cases hlt : nBlk s₀ - (c + 6) < 6
        · exact .inl ⟨by simp [eval, hcf', hlt], c + 6, hlt, hI'⟩
        · exact .inr ⟨by simp [eval, hcf', hlt], nBlk s₀ - (c + 6), by omega, c + 6, rfl, by omega, hI'⟩
      exact WP.loop (M := isa) I6 hstep (nBlk s₀) s ⟨0, rfl, by simpa using h, hI⟩
  refine WP.seq (WP.mono (testEdi_ok hI₂) fun s₃ ⟨hI₃, hzf⟩ => ?_)
  refine WP.seq (WP.mono (Q := Inv s₀ (nBlk s₀) (nBlk s₀)) ?_ fun s₄ hI₄ => hQ _ hI₄)
  refine WP.ite (decide (nBlk s₀ - c = 0)) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
  · have : c = nBlk s₀ := by have := hI₃.le; simp at h; omega
    exact WP.block_nil (this ▸ hI₃)
  · let I1 : Nat → State → Prop := fun m s => ∃ c, m = nBlk s₀ - c ∧ c < nBlk s₀ ∧ Inv s₀ c c s
    have hstep : ∀ m s, I1 m s → WP isa body1 s (fun s' =>
        (eval .ne s' = some false ∧ Inv s₀ (nBlk s₀) (nBlk s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, I1 m' s')) := by
      rintro m s ⟨c, rfl, hc, hI⟩
      refine WP.mono (body1_ok hp hc hI) fun s' ⟨hI', hzf'⟩ => ?_
      by_cases hlast : nBlk s₀ - (c + 1) = 0
      · have : c + 1 = nBlk s₀ := by omega
        exact .inl ⟨by simp [eval, hzf', hlast], this ▸ hI'⟩
      · exact .inr ⟨by simp [eval, hzf', hlast], nBlk s₀ - (c + 1), by omega, c + 1, rfl, by omega, hI'⟩
    have hlt : c < nBlk s₀ := by have := hI₃.le; simp at h; omega
    exact WP.loop (M := isa) I1 hstep (nBlk s₀ - c) s₃ ⟨c, rfl, hlt, hI₃⟩


end VG.Proof.Aes.X86.AesNi
