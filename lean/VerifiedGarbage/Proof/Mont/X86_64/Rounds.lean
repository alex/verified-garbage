import VerifiedGarbage.Proof.Mont.X86_64.Round

/-!
# Montgomery arithmetic on x86-64: the rounds of the multiplication

From a cleared accumulator (`zeros_ok`), `k` rounds leave `T_k < 2m` with
`2^(64k) T_k = A_k B + U m` (`rounds_ok`), `A_k` the low `k` words of `[a]`.
-/

namespace VG.Proof.Mont.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

theorem wordsVal_succ_top (m : Mem) (base : Addr) (d k : Nat) :
    wordsVal m base d (k + 1) = wordsVal m base d k + 2 ^ (64 * k) * (word m base (d + 8 * k)).toNat := by
  induction k generalizing d with
  | zero => simp [wordsVal]
  | succ k ih =>
    rw [wordsVal, ih (d + 8), wordsVal, pow64_succ, Nat.mul_add, Nat.mul_assoc,
      show d + 8 + 8 * k = d + 8 * (k + 1) by omega]
    omega

theorem regsVal_zero {s : State} {rs : List Reg} (h : ∀ r ∈ rs, s.gpr r = 0) : regsVal s rs = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rw [regsVal, h r (List.mem_cons_self ..), ih fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

theorem zeros_ok (s : State) : ∀ ts : List Reg,
    WP isa (.block (zeros ts)) s fun s' => (∀ t ∈ ts, s'.gpr t = 0) ∧ Keeps ts s s'
  | [] => WP.block_nil ⟨fun _ h => absurd h (List.not_mem_nil), fun _ _ => rfl, rfl, rfl, rfl⟩
  | t :: ts => by
    rw [zeros, List.map_cons, ← List.singleton_append, WP.block_append_iff]
    refine WP.mono (show WP isa (.block [.mov32 t (.imm 0)]) s
        (fun s₁ => s₁.gpr t = 0 ∧ Keeps [t] s s₁) by
      apply WP.of_runBlock
      simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
        State.setReg32, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
      refine ⟨rfl, fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [RegUpd.gpr_setReg, hr, ite_false]) fun s₁ ⟨z₁, k₁⟩ => ?_
    refine WP.mono (zeros_ok s₁ ts) fun s₂ ⟨z₂, k₂⟩ => ⟨fun q hq => ?_, (k₁.mono (by sub_regs)).trans
      (k₂.mono (by sub_regs))⟩
    by_cases hqt : q ∈ ts
    · exact z₂ q hqt
    · have : q = t := by simpa [hqt] using hq
      subst this; rw [k₂.1 _ hqt, z₁]

theorem wins_sub_acc_lt : ∀ n < 7, ∀ i < n + 2, ∀ r ∈ wins n i, r ∈ acc n := by decide

theorem wins_sub_acc {n : Nat} (hn : n < 7) (i : Nat) : ∀ r ∈ wins n i, r ∈ acc n := by
  rw [wins_mod]; exact wins_sub_acc_lt n hn _ (Nat.mod_lt _ (by omega))

theorem acc_regs_lt : ∀ n < 7, ∀ r ∈ acc n, r ≠ .rax ∧ r ≠ .rcx ∧ r ≠ .rdx ∧ r ≠ .rbp ∧ r ≠ .rdi := by
  decide

/-- `k` rounds, from a cleared accumulator. -/
theorem rounds_ok {M : Mod} (hn : M.n < 7) {a b m size : Nat}
    (ha : a + 8 * M.n ≤ size) (hb : b + 8 * M.n ≤ size) (hmo : M.mo + 8 * M.n ≤ size)
    (hinv : (m * M.minv.toNat + 1) % 2 ^ 64 = 0) :
    ∀ k ≤ M.n, ∀ {s : State} {base : Addr}, Scr s base size →
      wordsVal s.mem base M.mo M.n = m → wordsVal s.mem base b M.n < m →
      regsVal s (wins M.n 0) = 0 →
      WP isa (.block ((List.range k).flatMap (round M a b))) s fun s' =>
        (∃ U, 2 ^ (64 * k) * regsVal s' (wins M.n k) =
          wordsVal s.mem base a k * wordsVal s.mem base b M.n + U * m) ∧
        regsVal s' (wins M.n k) < 2 * m ∧
        Keeps (.rax :: .rcx :: .rdx :: .rbp :: acc M.n) s s'
  | 0, _, s, _, _, _, hB, h0 => WP.block_nil ⟨⟨0, by simp [h0, wordsVal]⟩, by rw [h0]; omega,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | k + 1, hk, s, base, hs, hm, hB, h0 => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (rounds_ok hn ha hb hmo hinv k (by omega) hs hm hB h0)
      fun s₁ ⟨⟨U, eU⟩, hT, k₁⟩ => ?_
    have hmem : s₁.mem = s.mem := k₁.2.1
    have hs₁ := hs.of_keeps k₁ (by
      intro h
      simp only [List.mem_cons] at h
      rcases h with h | h | h | h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact (acc_regs_lt _ hn _ h).2.2.2.2 rfl)
    refine WP.mono (round_ok hs₁ hn (i := k) (by omega) hb hmo (by rw [hmem, hm]) hinv
      (by rw [hmem]; exact hB) hT) fun s₂ ⟨⟨u, eu⟩, hT₂, k₂⟩ => ?_
    rw [hmem] at eu
    refine ⟨⟨U + 2 ^ (64 * k) * u, ?_⟩, hT₂, k₁.trans (k₂.mono fun q hq => ?_)⟩
    · calc 2 ^ (64 * (k + 1)) * regsVal s₂ (wins M.n (k + 1))
          = 2 ^ (64 * k) * (2 ^ 64 * regsVal s₂ (wins M.n (k + 1))) := by
            rw [Nat.mul_succ, Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ (64 * k) * regsVal s₁ (wins M.n k) +
            2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat * wordsVal s.mem base b M.n +
            2 ^ (64 * k) * u * m := by rw [eu]; simp only [Nat.mul_add, Nat.mul_assoc]
        _ = (wordsVal s.mem base a k + 2 ^ (64 * k) * (word s.mem base (a + 8 * k)).toNat) *
            wordsVal s.mem base b M.n + (U + 2 ^ (64 * k) * u) * m := by
            rw [eU, Nat.add_mul, Nat.add_mul]; omega
        _ = _ := by rw [wordsVal_succ_top]
    · simp only [List.mem_cons] at hq ⊢
      rcases hq with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (wins_sub_acc hn k q h))))

end VG.Proof.Mont.X86_64
