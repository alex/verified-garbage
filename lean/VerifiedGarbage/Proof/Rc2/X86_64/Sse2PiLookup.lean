import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Steps
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish

/-! # Verified constant-time SSE2 PITABLE lookup -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem piLookup_ok (s : State)
    (hwrite : InRegions s.wr (s.gpr .r8 + BitVec.ofNat 64 64) 16) :
    WP isa (.block Impl.Rc2.X86_64.Sse2.piLookup) s (fun s' =>
      s'.gpr .rax = (Spec.Rc2.pi ((s.gpr .rax).setWidth 8)).setWidth 64 ∧
      Keep [.rax, .rcx, .r10, .r11] s s') := by
  have hread : InRegions (s.rd ++ s.wr) (s.gpr .r8 + BitVec.ofNat 64 64) 16 := by
    obtain ⟨r, hr, hc⟩ := hwrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [Impl.Rc2.X86_64.Sse2.piLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, idx₁, ones₁, eights₁, saved₁, keep₁⟩ := start_ok s .r8 hread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff, List.range_eq_range']
  have inv₁ : ScanInv ((s.gpr .rax).setWidth 8) 0 s₁ :=
    ⟨input₁, zero₁.trans (acc_zero _ _).symm, idx₁, ones₁, eights₁⟩
  apply WP.mono (piSteps_ok 32 0 (by decide) s₁ _ inv₁)
  intro s₂ h₂
  rw [Impl.Rc2.X86_64.Sse2.finish, WP.block_append_iff]
  obtain ⟨s₃, run₃, reduced₃, keep₃⟩ := reduceOr_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep₂ : Keep [.rax, .r10] s₁ s₂ := h₂.2.1.weaken (by simp)
  have keep₃' : Keep [.rax, .r10] s₂ s₃ := keep₃.keep.weaken (by simp)
  have kept : Keep [.rax, .r10] s s₃ := (keep₁.trans keep₂).trans keep₃'
  have ptr : s₃.gpr .r8 = s.gpr .r8 := kept.reg .r8 (by decide)
  have wr₃ : InRegions s₃.wr (s₃.gpr .r8 + BitVec.ofNat 64 64) 16 := by
    rw [kept.wr, ptr]; exact hwrite
  have rd₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .r8 + BitVec.ofNat 64 64) 8 := by
    rw [kept.rd, kept.wr, ptr]
    obtain ⟨r, hr, hc⟩ := hread
    exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  have saved₃ : s₃.xmm .xmm8 = s₃.mem.readW (s₃.gpr .r8 + BitVec.ofNat 64 64) 128 := by
    rw [keep₃.xmm .xmm8 (by decide), h₂.2.2, saved₁, kept.mem, ptr]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := finishTail_ok s₃ .r8 (by decide) rd₃ wr₃ saved₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · rw [out₄, reduced₃, h₂.1.acc, reduce_acc, ite_eq_left ((s.gpr .rax).setWidth 8).isLt]
    simp [piWord, Spec.Rc2.pi]
  · exact (kept.trans (keep₄.weaken (by simp))).weaken (by simp)

end VG.Proof.Rc2.X86_64.Sse2
