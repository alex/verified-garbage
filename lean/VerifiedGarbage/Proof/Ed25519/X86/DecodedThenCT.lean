import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTDecodeInput

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

structure TestUnchanged (s t : State) : Prop where
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem Saved.test {s₀ s t : State} {base : BitVec 32} (h : Saved s₀ base s) (k : TestUnchanged s t) : Saved s₀ base t :=
  ⟨(congrFun k.gpr _).trans h.edi, (congrFun k.gpr _).trans h.esp, k.rd.trans h.rd, k.wr.trans h.wr,
    by rw [k.mem]; exact h.frame, by rw [k.mem]; exact h.saved⟩

theorem DecodeResult.test {base : BitVec 32} {p : Option Spec.Ed25519.Point} {s t : State}
    (h : DecodeResult base p s) (k : TestUnchanged s t) : DecodeResult base p t := by
  cases p with
  | none => exact (congrFun k.gpr _).trans h
  | some p => exact ⟨(congrFun k.gpr _).trans h.1, by rw [k.mem]; exact h.2⟩

theorem decodedThen_ct (base : BitVec 32) (p : Option Spec.Ed25519.Point) (P₁ P₂ : State → Prop) (next : Prog isa)
    (hP₁ : ∀ s t, TestUnchanged s t → P₁ s → P₁ t)
    (hP₂ : ∀ s t, TestUnchanged s t → P₂ s → P₂ t)
    (hn : ∀ a, p = some a → RelCT isa
      (fun s t => (P₁ s ∧ point (env s.mem base) 0 1 2 3 = a) ∧
        (P₂ t ∧ point (env t.mem base) 0 1 2 3 = a)) next (fun _ _ => True)) :
    RelCT isa (fun s t => (P₁ s ∧ DecodeResult base p s) ∧ (P₂ t ∧ DecodeResult base p t))
      (decodedThen next) (fun _ _ => True) := by
  have ht : RelCT isa (fun s t => (P₁ s ∧ DecodeResult base p s) ∧ (P₂ t ∧ DecodeResult base p t))
      (.block [.alu .test .eax (.reg .eax)]) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint []) _ (by taint_decide)
    exact fun _ _ _ => regsTaint_agree (by simp)
  have hw (P : State → Prop) (hP : ∀ s t, TestUnchanged s t → P s → P t) (s : State)
      (h : P s ∧ DecodeResult base p s) :
      WP isa (.block [.alu .test .eax (.reg .eax)]) s fun t => P t ∧ DecodeResult base p t ∧ t.zf = some (!p.isSome) := by
    refine Wp.wp_test fun t kt zt => WP.block_nil ?_
    have k : TestUnchanged s t := ⟨kt.gpr, kt.mem, kt.rd, kt.wr⟩
    refine ⟨hP s t k h.1, h.2.test k, ?_⟩
    rw [zt, BitVec.and_self, decodeResult_flag h.2]
    cases p <;> rfl
  have hp := ht.wp (fun s t h => ⟨hw P₁ hP₁ s h.1, hw P₂ hP₂ t h.2⟩)
  rw [decodedThen]
  refine VG.RelCT.seq hp (VG.RelCT.ite (M := isa) ?_ ?_ ?_)
  · intro s t h
    change s.zf.map Bool.not = t.zf.map Bool.not
    rw [h.2.1.2.2, h.2.2.2.2]
  · cases p with
    | none =>
      apply VG.RelCT.of_false
      intro s t h
      have he := h.2
      change s.zf.map Bool.not = some true at he
      rw [h.1.2.1.2.2] at he
      contradiction
    | some a =>
      exact (hn a rfl).mono
        (fun _ _ h => ⟨⟨h.1.2.1.1, h.1.2.1.2.1.2⟩, ⟨h.1.2.2.1, h.1.2.2.2.1.2⟩⟩) (fun _ _ h => h)
  · exact recoverInvalid_ct.mono (fun _ _ _ => trivial) (fun _ _ h => h)

end VG.Proof.Ed25519.X86
