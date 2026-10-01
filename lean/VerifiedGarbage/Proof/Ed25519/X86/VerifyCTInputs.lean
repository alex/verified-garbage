import VerifiedGarbage.Proof.Ed25519.X86.VerifyCTLit
import VerifiedGarbage.Proof.Ed25519.X86.VerifyContract
import VerifiedGarbage.Proof.Ed25519.X86.PointDecodeCT

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

def VerifySaved (s₀ t₀ s t : State) : Prop := Saved s₀ (arg s₀ 3) s ∧ Saved t₀ (arg t₀ 3) t

structure VerifyCTFacts (s t : State) : Prop where
  left : verifyLocal.pre s
  right : verifyLocal.pre t
  pub : verifyLocal.pub s t

theorem VerifyCTFacts.args {s t : State} (h : VerifyCTFacts s t) (i : Nat) (hi : i < 4) : arg s i = arg t i := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  exacts [h.pub.2.1, h.pub.2.2.1, h.pub.2.2.2.1, h.pub.2.2.2.2.1]

theorem loadSlicePointer_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i skip : Nat)
    (hi : i ≤ 2) (hk : skip = 0 ∨ skip = 32) :
    RelCT isa (VerifySaved s₀ t₀) (.block (loadSlicePointer i skip))
      (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi) := by
  have hc : RelCT isa (VerifySaved s₀ t₀) (.block (loadSlicePointer i skip)) (fun _ _ => True) := by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    all_goals rcases hk with rfl | rfl
    all_goals
      apply VG.RelCT.taint (A := taint) (regsTaint [.esp]) _ (by taint_decide)
      intro s t hp
      exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸
        (hp.1.esp.trans (h.pub.1.trans hp.2.esp.symm)))
  have hp := ctWithRuns hc (fun _ _ hs => ⟨loadSlicePointer_ok (verify_pre h.left).scratch hs.1 (by omega),
    loadSlicePointer_ok (verify_pre h.right).scratch hs.2 (by omega)⟩)
  apply hp.mono (fun _ _ h => h)
  intro s t ⟨_, a, b, _, hs, ht⟩
  exact ⟨hs.1.edi.trans ((h.args 3 (by decide)).trans ht.1.edi.symm),
    hs.2.1.trans ((congrArg (· + BitVec.ofNat 32 skip) (h.args i (by omega))).trans ht.2.1.symm)⟩

theorem copyWords96_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
    (.block (copyWords 96 8)) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
  intro s t h
  apply regsTaint_agree
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h.1, h.2]

theorem inputSlice96_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) (i : Nat) (hi : i ≤ 2) :
    RelCT isa (VerifySaved s₀ t₀) (.block (inputSliceWords i 0 96 8)) (fun _ _ => True) := by
  exact ctBlockAppend (loadSlicePointer_ct h i 0 hi (Or.inl rfl)) copyWords96_ct

theorem verifyScalar_ct {s₀ t₀ : State} (h : VerifyCTFacts s₀ t₀) :
    RelCT isa (VerifySaved s₀ t₀) (.block verifyScalar) (fun _ _ => True) := by
  have hc : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi ∧ s.gpr .esi = t.gpr .esi)
      (.block (copyWords 64 8 ++ scalarSubtract ++ ([.alu .test .ebx (.reg .ebx)] : List Instr))) (fun _ _ => True) := by
    apply VG.RelCT.taint (A := taint) (regsTaint [.edi, .esi]) _ (by taint_decide)
    intro s t h
    apply regsTaint_agree
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h.1, h.2]
  simp only [verifyScalar, inputSliceWords, List.append_assoc]
  exact ctBlockAppend (loadSlicePointer_ct h 1 32 (by decide) (Or.inr rfl)) hc

theorem verifyFinish_ct : RelCT isa (fun s t => s.gpr .edi = t.gpr .edi)
    (.block verifyFinish) (fun _ _ => True) := by
  apply VG.RelCT.taint (A := taint) (regsTaint [.edi]) _ (by taint_decide)
  intro s t h
  exact regsTaint_agree (fun r hr => (List.mem_singleton.mp hr) ▸ h)

end VG.Proof.Ed25519.X86
