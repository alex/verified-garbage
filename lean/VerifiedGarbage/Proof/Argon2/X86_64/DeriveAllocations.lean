import VerifiedGarbage.Proof.Argon2.X86_64.DeriveHashInputs

/-! The exact matrix and output allocations of the signature remain writable. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_matrix_region {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
  have words := private_words h prepared
  change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
  rw [words.matrix, ← h.blocks]; rfl

theorem private_local_cover {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 272) : Covers [⟨t.gpr .rbp, n⟩] t.wr := by
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨⟨t.gpr .rbp, 272⟩, ?_, ?_⟩
  · rw [prepared.wr, prepared.bp]
    exact frameStart_locals s _
  · unfold Region.Contains at hc ⊢
    exact Nat.le_trans hc bound

theorem private_matrix_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩] t.wr := by
  have words := private_words h prepared
  have member : abiMatrix s ∈ t.wr := private_wr_member prepared _ (by rw [h.wr]; exact List.mem_cons_self ..)
  have matrix : (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
    change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
    rw [words.matrix, ← h.blocks]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiMatrix s, member, matrix ▸ hc⟩

theorem private_output_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FinalOutput.output t, (abiParams s).tagLen⟩] t.wr := by
  have words := private_words h prepared
  have member : abiOutput s ∈ t.wr := private_wr_member prepared _ (by
    rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiOutput s, member, output ▸ hc⟩

theorem private_work_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (n : Nat) (bound : n ≤ 16384) :
    Covers [⟨FinalOutput.work t, n⟩] t.wr := by
  have words := private_words h prepared
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨abiWork s, private_work_member h prepared, ?_⟩
  change Region.Contains ⟨abiWord s 80, 16384⟩ p k
  have pointer : FinalOutput.work t = abiWord s 80 := words.work
  rw [pointer] at hc
  unfold Region.Contains at hc ⊢
  exact Nat.le_trans hc bound

end VG.Proof.Argon2.X86_64.Derive
