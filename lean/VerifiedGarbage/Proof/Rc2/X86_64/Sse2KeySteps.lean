import VerifiedGarbage.Proof.Rc2.X86_64.Sse2KeyStart

/-! # Composing eight-candidate schedule scans -/

namespace VG.Proof.Rc2.X86_64.Sse2

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.Rc2.X86_64

structure KeyScanInv (f : Nat → BitVec 16) (x : Byte) (n : Nat) (s : State) : Prop where
  input : s.xmm .xmm0 = broadcast x
  acc : s.xmm .xmm1 = Sse2.acc f x.toNat n
  indices : s.xmm .xmm2 = Impl.Rc2.X86_64.Sse2.indices n
  ones : s.xmm .xmm6 = Impl.Rc2.X86_64.Sse2.ones
  eights : s.xmm .xmm7 = Impl.Rc2.X86_64.Sse2.eights

theorem keyLoad_ok (s : State) (n : Nat)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 16) :
    ∃ s', runBlock isa [.movdquLoad .xmm4 (memOp .rdi (16 * n))] s = some s' ∧
      s'.xmm .xmm4 = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 128 ∧
      KeepX [] [.xmm4] s s' := by
  refine ⟨_, by
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.load128,
      State.ea, memOp, offset_nat, hread, ite_true, Option.map_some]
    rfl, ?_⟩
  constructor
  · exact xmm_setXmm_self _ _ _
  · constructor
    · exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      exact xmm_setXmm_of_ne _ _ hr

theorem keyStep_ok (s : State) (f : Nat → BitVec 16) (x : Byte) (n : Nat) (hn : n < 8)
    (hinv : KeyScanInv f x n s)
    (hf : ∀ i < 64, f i = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16)
    (hread : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * n)) 16) :
    WP isa (.block (Impl.Rc2.X86_64.Sse2.keyStep n)) s (fun s' =>
      KeyScanInv f x (n + 1) s' ∧ Keep [] s s' ∧ s'.xmm .xmm8 = s.xmm .xmm8) := by
  rw [Impl.Rc2.X86_64.Sse2.keyStep, WP.block_append_iff]
  obtain ⟨s₁, run₁, val₁, keep₁⟩ := keyLoad_ok s n hread
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  obtain ⟨s₂, run₂, val₂, idx₂, keep₂⟩ := select_ok s₁
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  refine ⟨?_, keep₁.keep.trans keep₂.keep, ?_⟩
  · constructor
    · rw [keep₂.xmm .xmm0 (by decide), keep₁.xmm .xmm0 (by decide)]
      exact hinv.input
    · rw [val₂, keep₁.xmm .xmm1 (by decide), keep₁.xmm .xmm0 (by decide),
        keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm6 (by decide), val₁,
        hinv.acc, hinv.input, hinv.indices, hinv.ones]
      apply acc_step f x n (by omega)
      intro j hj
      rw [word_readW _ _ hj, hf (8 * n + j) (by omega)]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact congrArg (fun d => s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 d) 16) (by omega)
    · rw [idx₂, keep₁.xmm .xmm2 (by decide), keep₁.xmm .xmm7 (by decide),
        hinv.indices, hinv.eights]
      exact indices_next n
    · rw [keep₂.xmm .xmm6 (by decide), keep₁.xmm .xmm6 (by decide)]
      exact hinv.ones
    · rw [keep₂.xmm .xmm7 (by decide), keep₁.xmm .xmm7 (by decide)]
      exact hinv.eights
  · rw [keep₂.xmm .xmm8 (by decide), keep₁.xmm .xmm8 (by decide)]

theorem keySteps_ok (count n : Nat) (hbound : n + count ≤ 8)
    (s : State) (f : Nat → BitVec 16) (x : Byte) (hinv : KeyScanInv f x n s)
    (hf : ∀ i < 64, f i = s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16)
    (hread : ∀ i < 8, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16) :
    WP isa (.block ((List.range' n count).flatMap Impl.Rc2.X86_64.Sse2.keyStep)) s
      (fun s' => KeyScanInv f x (n + count) s' ∧ Keep [] s s' ∧
        s'.xmm .xmm8 = s.xmm .xmm8) := by
  induction count generalizing n s with
  | zero =>
    apply WP.block_nil
    exact ⟨hinv, ⟨fun _ _ => rfl, rfl, rfl, rfl⟩, rfl⟩
  | succ count ih =>
    rw [List.range'_succ, List.flatMap_cons, WP.block_append_iff]
    apply WP.mono (keyStep_ok s f x n (by omega) hinv hf (hread n (by omega)))
    intro s₁ h₁
    have hf₁ : ∀ i < 64, f i = s₁.mem.readW (s₁.gpr .rdi + BitVec.ofNat 64 (2 * i)) 16 := by
      rw [h₁.2.1.mem, h₁.2.1.reg .rdi (by simp)]; exact hf
    have hr₁ : ∀ i < 8, InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .rdi + BitVec.ofNat 64 (16 * i)) 16 := by
      rw [h₁.2.1.rd, h₁.2.1.wr, h₁.2.1.reg .rdi (by simp)]; exact hread
    apply WP.mono (ih (n + 1) (by omega) s₁ h₁.1 hf₁ hr₁)
    intro s₂ h₂
    refine ⟨?_, h₁.2.1.trans h₂.2.1, h₂.2.2.trans h₁.2.2⟩
    have he : n + 1 + count = n + (count + 1) := by omega
    exact he ▸ h₂.1

end VG.Proof.Rc2.X86_64.Sse2
