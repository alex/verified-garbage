import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Scalar
import VerifiedGarbage.Proof.MlKem.X86_64.S4Verified

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_rej_ntt_poly4_avx2`, verified

The contract of the proofs (`r4K`) implies the shared one of `Spec/`: a seed
with 256 coefficients in the 1008 bytes both implementations sample from has
them within those bounds (`rejNTT_some`), and one without has none within the
least bound (`rejNTT_none`).
-/

namespace VG.Proof.MlDsa.X86_64.Rej4

open VG VG.X86_64
open VG.Proof.MlDsa.Sample (rnFold rejNTT_some rejNTT_none)
open VG.Proof.MlDsa.X86_64.Sample (leakBytes_inj)
open VG.Spec.MlDsa (G)

theorem seed4_eq : Spec.MlDsa.seed4 = Spec.MlKem.seed4 := rfl
theorem poly4_eq : Spec.MlDsa.poly4 = Spec.MlKem.poly4 := rfl

theorem r4_post {s s' : State} (h : r4K.post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Spec.MlDsa.Reduced s'.mem (Spec.MlDsa.poly4 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ b : Spec.MlDsa.Bounds, Spec.MlDsa.rejNTTPoly b.rejNTT
          (Spec.MlDsa.seed4 s.mem (s.gpr .rdi) k) = some (Spec.MlDsa.polyAt s'.mem (Spec.MlDsa.poly4 (s.gpr .rsi) k))) ∨
        (r = 0 ∧ ∃ k < 4, Spec.MlDsa.rejNTTPoly Spec.MlDsa.minBounds.rejNTT
          (Spec.MlDsa.seed4 s.mem (s.gpr .rdi) k) = none)) := by
  obtain ⟨hr, hp⟩ := h
  intro r
  simp only [seed4_eq, poly4_eq]
  by_cases hall : ((List.range 4).all fun k =>
      (rnFold [] (G (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length == 256) = true
  · rw [ite_eq_left hall] at hr
    have hs : ∀ k < 4, (rnFold [] (G (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) 1008)).length = 256 := fun k hk => by
      simpa using List.all_eq_true.mp hall k (List.mem_range.mpr hk)
    refine ⟨fun _ k hk => (hp k hk (hs k hk)).1, .inl ⟨hr, fun k hk => ⟨{ Spec.MlDsa.minBounds with rejNTT := 1008 }, ?_⟩⟩⟩
    show Spec.MlDsa.rejNTTPoly 1008 _ = _
    rw [rejNTT_some (hs k hk), (hp k hk (hs k hk)).2]
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, not_forall, beq_iff_eq] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, rejNTT_none (B := 1008) (by decide) (by decide) hk'⟩

theorem rej4_verified (c : Prog isa) (hc : ∀ σ, r4K.pre σ → ∃ t s', Exec isa c σ t s' ∧ abiPreserved σ s' ∧ r4K.post σ s')
    (ht : ConstantTime isa r4K.pre r4K.pub c) : Verified X86_64.target c (Spec.MlDsa.rejNTT4Contract X86_64.abi 24) :=
  Verified.of_correct hc ht
    { pre := by sig_implies_pre [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K,
        X86_64.abi, X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, r4K, X86_64.abi, X86_64.argRegs]
        exact r4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] at h
        sig_split h
        sig_reduce [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs]
        sig_simp [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact leakBytes_inj ‹_›
      sat := by
        sig_implies_sat [Spec.MlDsa.rejNTT4Contract, Spec.MlDsa.rejNTT4Sig, r4K, MlKem.X86_64.sample4K, X86_64.abi,
          X86_64.argRegs] [MlKem.X86_64.sample4Sat] using MlKem.X86_64.sample4Sat }

theorem rejNTT4Avx2_verified : Verified X86_64.target Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4Avx2
    (Spec.MlDsa.rejNTT4Contract X86_64.abi 24) := rej4_verified _ correct ct

theorem rejNTT4_verified : Verified X86_64.target Impl.MlDsa.X86_64.Sample.Rej4.rejNTT4
    (Spec.MlDsa.rejNTT4Contract X86_64.abi 24) := rej4_verified _ correct_scalar ct_scalar

end VG.Proof.MlDsa.X86_64.Rej4
