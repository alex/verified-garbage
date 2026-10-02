import VerifiedGarbage.Proof.MlKem.X86_64.S4CT

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4_avx2`, verified

The contract of the proof (`sample4K`) implies the shared one of `Spec/`.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64

/-- A state satisfying the precondition. -/
def sample4Sat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x4000 | .rsp => 0x10000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 136⟩]
  wr := [⟨0x2000, 4096⟩, ⟨0x4000, 8192⟩]

theorem sample4_post {s s' : State} (h : sample4K.post s s') :
    let r := (s'.gpr .rax).setWidth 32
    (r = 1 → ∀ k < 4, Spec.MlKem.Reduced s'.mem (Spec.MlKem.poly4 (s.gpr .rsi) k)) ∧
      ((r = 1 ∧ ∀ k < 4, ∃ iters, Spec.MlKem.sampleNTT iters (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) =
          some (Spec.MlKem.polyAt s'.mem (Spec.MlKem.poly4 (s.gpr .rsi) k))) ∨
        (r = 0 ∧ ∃ k < 4, Spec.MlKem.sampleNTT Spec.MlKem.minIterations
          (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) = none)) := by
  obtain ⟨hr, hp⟩ := h
  intro r
  by_cases hall : ((List.range 4).all fun k =>
      (Spec.MlKem.sampleNTT Spec.MlKem.minIterations (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k)).isSome) = true
  · rw [ite_eq_left hall] at hr
    have hs : ∀ k < 4, ∃ f, Spec.MlKem.sampleNTT Spec.MlKem.minIterations
        (Spec.MlKem.seed4 s.mem (s.gpr .rdi) k) = some f := fun k hk => by
      have := List.all_eq_true.mp hall k (List.mem_range.mpr hk)
      exact Option.isSome_iff_exists.mp this
    refine ⟨fun _ k hk => ?_, .inl ⟨hr, fun k hk => ?_⟩⟩
    · obtain ⟨f, e⟩ := hs k hk; exact (hp k hk f e).1
    · obtain ⟨f, e⟩ := hs k hk
      exact ⟨Spec.MlKem.minIterations, by rw [e, (hp k hk f e).2]⟩
  · rw [ite_eq_right hall] at hr
    refine ⟨fun h1 => absurd (hr.symm.trans h1) (by decide), .inr ⟨hr, ?_⟩⟩
    simp only [List.all_eq_true, List.mem_range, not_forall] at hall
    obtain ⟨k, hk, hk'⟩ := hall
    exact ⟨k, hk, Option.not_isSome_iff_eq_none.mp hk'⟩

theorem sample4_verified : Verified X86_64.target Impl.MlKem.X86_64.Sample4.sampleNTT4Avx2
    (Spec.MlKem.sampleNTT4Contract X86_64.abi 24) :=
  Verified.of_correct S4.correct S4.ct
    { pre := by sig_implies_pre [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, sample4K, X86_64.abi,
        X86_64.argRegs]
      post := by
        intro s s' _ h
        sig_post [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs]
        exact sample4_post h
      pub := by
        intro s₁ s₂ _ _ h
        sig_pub [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs] at h
        sig_split h
        sig_reduce [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs]
        sig_simp [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, sample4K, X86_64.abi, X86_64.argRegs]
          [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, forall_const, true_and]
        sig_and_intros
        sig_close
        all_goals first | with_reducible assumption | exact map_toNat_inj ‹_›
      sat := by
        sig_implies_sat [Spec.MlKem.sampleNTT4Contract, Spec.MlKem.sampleNTT4Sig, sample4K, X86_64.abi,
          X86_64.argRegs] [sample4Sat] using sample4Sat }

end VG.Proof.MlKem.X86_64
