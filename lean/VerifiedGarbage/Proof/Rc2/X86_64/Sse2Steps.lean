import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Start

/-! # Composing eight-candidate PITABLE scans -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.Impl.Rc2.X86_64

def piWord (i : Nat) : BitVec 16 := (Spec.Rc2.piTable.getD i 0).setWidth 16

structure ScanInv (x : Byte) (n : Nat) (s : State) : Prop where
  input : s.xmm .xmm0 = broadcast x
  acc : s.xmm .xmm1 = Sse2.acc piWord x.toNat n
  indices : s.xmm .xmm2 = Impl.Rc2.X86_64.Sse2.indices n
  ones : s.xmm .xmm6 = Impl.Rc2.X86_64.Sse2.ones
  eights : s.xmm .xmm7 = Impl.Rc2.X86_64.Sse2.eights

theorem piStep_ok (s : State) (x : Byte) (n : Nat) (hn : n < 32) (hinv : ScanInv x n s) :
    WP isa (.block (Impl.Rc2.X86_64.Sse2.piStep n)) s (fun s' =>
      ScanInv x (n + 1) s' ∧ Keep [.r10] s s' ∧ s'.xmm .xmm8 = s.xmm .xmm8) := by
  rw [Impl.Rc2.X86_64.Sse2.piStep, WP.block_append_iff]
  obtain ⟨s₁, run₁, val₁, keep₁⟩ := loadConst_ok s .xmm4 (by decide)
    (Impl.Rc2.X86_64.Sse2.piValues n)
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, val₂, idx₂, keep₂⟩ := select_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine ⟨?_, keep₁.keep.trans (keep₂.keep.weaken (by simp)), ?_⟩
  · constructor
    · rw [keep₂.xmm .xmm0 (by decide), keep₁.xmm .xmm0 (by decide)]
      exact hinv.input
    · rw [val₂, keep₁.xmm .xmm1 (by decide), keep₁.xmm .xmm0 (by decide),
        keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm6 (by decide), val₁,
        hinv.acc, hinv.input, hinv.indices, hinv.ones]
      apply acc_step piWord x n hn
      intro j hj
      exact word_ofWords _ hj
    · rw [idx₂, keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm7 (by decide),
        hinv.indices, hinv.eights]
      exact indices_next n
    · rw [keep₂.xmm .xmm6 (by decide), keep₁.xmm .xmm6 (by decide)]
      exact hinv.ones
    · rw [keep₂.xmm .xmm7 (by decide), keep₁.xmm .xmm7 (by decide)]
      exact hinv.eights
  · rw [keep₂.xmm .xmm8 (by decide), keep₁.xmm .xmm8 (by decide)]

theorem piSteps_ok (count n : Nat) (hbound : n + count ≤ 32)
    (s : State) (x : Byte) (hinv : ScanInv x n s) :
    WP isa (.block ((List.range' n count).flatMap Impl.Rc2.X86_64.Sse2.piStep)) s
      (fun s' => ScanInv x (n + count) s' ∧ Keep [.r10] s s' ∧
        s'.xmm .xmm8 = s.xmm .xmm8) := by
  induction count generalizing n s with
  | zero =>
    apply WP.block_nil
    exact ⟨hinv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩
  | succ count ih =>
    rw [List.range'_succ, List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (piStep_ok s x n (by omega) hinv)
    intro s₁ h₁
    apply WP.mono (ih (n + 1) (by omega) s₁ h₁.1)
    intro s₂ h₂
    refine ⟨?_, h₁.2.1.trans h₂.2.1, h₂.2.2.trans h₁.2.2⟩
    have he : n + 1 + count = n + (count + 1) := by omega
    exact he ▸ h₂.1

end VG.Proof.Rc2.X86_64.Sse2
