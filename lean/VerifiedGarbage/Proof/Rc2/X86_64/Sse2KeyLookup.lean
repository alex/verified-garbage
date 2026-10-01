import VerifiedGarbage.Proof.Rc2.X86_64.Sse2KeySteps
import VerifiedGarbage.Proof.Rc2.X86_64.Sse2Finish

/-! # Verified constant-time SSE2 schedule lookup -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.Impl.Rc2.X86_64

theorem schedule_readWord (m : Mem) (p : Addr) (i : Nat) (hi : i < 64) :
    m.readW (p + BitVec.ofNat 64 (2 * i)) 16 = (Spec.Rc2.scheduleAt m p).getD i 0 := by
  rw [scheduleAt_getD _ _ _ hi]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [Mem.readW, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, decide_eq_true hj, Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  by_cases h : j < 8
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.or_false,
      Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, BitVec.add_zero]
  · have hj' : j - 8 < 8 := by omega
    simp only [h, decide_false, Bool.not_false]
    have hdiv : j / 8 = 1 := by omega
    have hmod : j % 8 = j - 8 := by omega
    rw [hdiv, hmod]
    have hp : p + BitVec.ofNat 64 (2 * i) + BitVec.ofNat 64 1 =
        p + BitVec.ofNat 64 (2 * i + 1) := by rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hp]
    simp (disch := omega) only [BitVec.getLsbD_of_ge, decide_eq_true,
      Bool.true_and, Bool.false_or]

theorem keyLookup_ok (s : State)
    (hread : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16)
    (hwrite : InRegions s.wr (s.gpr .rdx + BitVec.ofNat 64 64) 16) :
    WP isa (.block Impl.Rc2.X86_64.Sse2.keyLookup) s (fun s' =>
      s'.gpr .rax = ((Spec.Rc2.scheduleAt s.mem (s.gpr .rdi)).getD
        ((s.gpr .rax).setWidth 6).toNat 0).setWidth 64 ∧
      Keep [.rax, .rcx, .r8, .r9, .r10, .r11] s s') := by
  have hsread : InRegions (s.rd ++ s.wr) (s.gpr .rdx + BitVec.ofNat 64 64) 16 := by
    obtain ⟨r, hr, hc⟩ := hwrite
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  rw [Impl.Rc2.X86_64.Sse2.keyLookup, List.append_assoc, WP.block_append_iff]
  obtain ⟨s₁, run₁, input₁, zero₁, idx₁, ones₁, eights₁, saved₁, keep₁⟩ := keyStart_ok s .rdx hsread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  rw [WP.block_append_iff, List.range_eq_range']
  let x : Byte := ((s.gpr .rax).setWidth 6).setWidth 8
  let f (i : Nat) := s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16
  have inv₁ : KeyScanInv f x 0 s₁ :=
    ⟨input₁, zero₁.trans (acc_zero _ _).symm, idx₁, ones₁, eights₁⟩
  have hf₁ : ∀ i < 64, f i = s₁.mem.readW (s₁.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16 := by
    rw [keep₁.mem, keep₁.reg .rdi (by decide)]
    intro _ _; rfl
  have hr₁ : ∀ i < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16 := by
    rw [keep₁.rd, keep₁.wr, keep₁.reg .rdi (by decide)]; exact hread
  apply WP.mono (keySteps_ok 8 0 (by decide) s₁ f x inv₁ hf₁ hr₁)
  intro s₂ h₂
  rw [Impl.Rc2.X86_64.Sse2.finish, WP.block_append_iff]
  obtain ⟨s₃, run₃, reduced₃, keep₃⟩ := reduceOr_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have keep₂ : Keep [.rax, .r10] s₁ s₂ := h₂.2.1.weaken (by simp)
  have keep₃' : Keep [.rax, .r10] s₂ s₃ := keep₃.keep.weaken (by simp)
  have kept : Keep [.rax, .r10] s s₃ := (keep₁.trans keep₂).trans keep₃'
  have ptr : s₃.gpr .rdx = s.gpr .rdx := kept.reg .rdx (by decide)
  have wr₃ : InRegions s₃.wr (s₃.gpr .rdx + BitVec.ofNat 64 64) 16 := by
    rw [kept.wr, ptr]; exact hwrite
  have rd₃ : InRegions (s₃.rd ++ s₃.wr) (s₃.gpr .rdx + BitVec.ofNat 64 64) 8 := by
    rw [kept.rd, kept.wr, ptr]
    obtain ⟨r, hr, hc⟩ := hsread
    exact ⟨r, hr, by unfold Region.Contains at hc ⊢; omega⟩
  have saved₃ : s₃.xmm .xmm8 = s₃.mem.readW (s₃.gpr .rdx + BitVec.ofNat 64 64) 128 := by
    rw [keep₃.xmm .xmm8 (by decide), h₂.2.2, saved₁, kept.mem, ptr]
  obtain ⟨s₄, run₄, out₄, keep₄⟩ := finishTail_ok s₃ .rdx (by decide) rd₃ wr₃ saved₃
  refine WP.of_runBlock ⟨s₄, run₄, ?_⟩
  constructor
  · have xb : x.toNat < 64 := by
      simp only [x, BitVec.toNat_setWidth]
      have h := ((s.gpr .rax).setWidth 6).isLt
      simp only [BitVec.toNat_setWidth] at h
      omega
    have xe : x.toNat = ((s.gpr .rax).setWidth 6).toNat := by
      simp only [x, BitVec.toNat_setWidth]
      have h := ((s.gpr .rax).setWidth 6).isLt
      simp only [BitVec.toNat_setWidth] at h
      omega
    rw [out₄, reduced₃, h₂.1.acc, reduce_acc, ite_eq_left xb]
    dsimp only [f]
    rw [schedule_readWord _ _ _ xb, xe]
  · exact (kept.trans (keep₄.weaken (by simp))).weaken (by simp)

end VG.Proof.Rc2.X86_64.Sse2
