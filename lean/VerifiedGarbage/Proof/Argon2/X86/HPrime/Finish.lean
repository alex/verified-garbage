import VerifiedGarbage.Proof.Argon2.X86.HPrime.Chain

/-!
# Argon2 H′ on x86 (32-bit): the output from the first digest

`finish_ok`: `finishOutput` writes H′ to the output, from the first digest:
the digest itself for at most 64 bytes, and otherwise its prefix, the chain
and the last hash (`extend_ok`), of the 33 to 64 bytes left.
-/

namespace VG.Proof.Argon2.X86.HPrime

open VG VG.X86 VG.Spec.Blake2
open VG.Impl.Argon2.X86.HPrime (next emitPrefix cmpLeft chain extendDigest finishOutput leftOff)
open VG.Proof.Sha256.X86.Stream (Upd wp_movm)
open VG.Proof.Argon2 (chainDigest chainPrefixes)

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- What the chain leaves: the output after `j` iterations and the last hash. -/
def Extended (s₀ : State) (e : BitVec 32) (V : List Byte) (t : State) : Prop :=
  ∃ j, Body s₀ t ∧ t.gpr .ebp = e ∧ Out s₀ t (chainOut V j) ∧
    (digest s₀ t).take (ol s₀ - (32 + 32 * j)) =
      Spec.Argon2.H (ol s₀ - (32 + 32 * j)) (chainDigest j V) ∧
    33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀

theorem extend_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) (hol : 65 ≤ ol s₀) :
    WP isa extendDigest s (Extended s₀ (s.gpr .ebp) (digest s₀ s)) := by
  have hs := hp.scr_fits
  have hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold extendDigest
  refine WP.seq ((emit_ok hp b o (by simp only [List.length_nil]; omega)).mono
    fun s₁ ⟨b₁, e₁, o₁, d₁⟩ => ?_)
  rw [List.nil_append, show (digest s₀ s).take 32 = chainOut (digest s₀ s) 0 by
    simp [chainOut, chainPrefixes]] at o₁
  have i₁ : ChainInv s₀ (s.gpr .ebp) (digest s₀ s) 0 s₁ := ⟨b₁, e₁, o₁, d₁⟩
  refine WP.seq ((cmp_ok hp b₁ o₁).mono fun s₂ ⟨cf₂, k₂, m₂⟩ => ?_)
  rw [chainOut_length hV] at cf₂
  have i₂ : ChainInv s₀ (s.gpr .ebp) (digest s₀ s) 0 s₂ :=
    ⟨b₁.keeps hp k₂, k₂.ebp.trans e₁, o₁.keeps hp k₂, by show bytesAt _ _ _ = _; rw [m₂]; exact d₁⟩
  have hIte : WP isa (.ite .b (.block []) chain) s₂ fun t => ∃ j, ChainInv s₀ (s.gpr .ebp) (digest s₀ s) j t ∧
      33 ≤ ol s₀ - (32 + 32 * j) ∧ ol s₀ - (32 + 32 * j) ≤ 64 ∧ 32 + 32 * j ≤ ol s₀ := by
    refine WP.ite (decide (ol s₀ - (32 + 32 * 0) < 65)) cf₂ (fun h => WP.block_nil ⟨0, i₂, ?_⟩)
      (fun h => (chain_ok hp hV i₂ ?_).mono fun t h => h)
    · simp only [decide_eq_true_eq] at h; omega
    · simp only [decide_eq_false_iff_not] at h; omega
  refine WP.seq (hIte.mono fun s₃ ⟨j, i₃, l₁, l₂, l₃⟩ => ?_)
  have rl : InRegions (s₃.rd ++ s₃.wr) (addr (scr s₀) leftOff) 4 := by
    rw [i₃.body.rd, i₃.body.wr]
    exact ⟨scrR s₀, by simp [hp.wr], Proof.Sha256.X86.Stream.contains_addr (by decide) (by decide) hs⟩
  refine WP.seq (wp_movm (VG.Proof.Sha512.X86.ea_of i₃.body.ebx leftOff) rl fun s₄ u₄ => WP.block_nil ?_)
  have k₄ : Keeps (scr s₀) (esp₀ s₀) s₃ s₄ := Keeps.same (u₄.other _ (by decide)) (u₄.other _ (by decide))
    (u₄.other _ (by decide)) u₄.mem u₄.rd u₄.wr
  have b₄ := i₃.body.keeps hp k₄
  have edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (ol s₀ - (32 + 32 * j)) := by
    rw [u₄.gpr, i₃.out.left, chainOut_length hV]
  refine (next_ok (b₄.ctx hp) edx₄ (by omega) l₂).mono fun t ⟨d, k⟩ => ?_
  have K := k₄.trans k
  refine ⟨j, i₃.body.keeps hp K, by rw [K.ebp, i₃.ebp], i₃.out.keeps hp K, ?_, l₁, l₂, l₃⟩
  rw [Proof.Argon2.H_stream, ← i₃.digest]
  rw [u₄.mem] at d
  exact congrArg (List.take _) d

/-- `finishOutput` writes H′ of the input `I` from its first digest. -/
theorem finish_ok {s : State} (b : Body s₀ s) (o : Out s₀ s []) {I : List Byte}
    (hd : (digest s₀ s).take (min (ol s₀) 64) =
      Spec.Argon2.H (min (ol s₀) 64) (Spec.Argon2.le32 (ol s₀) ++ I)) :
    WP isa finishOutput s fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      bytesAt t.mem ((op s₀).setWidth 64) (ol s₀) = Spec.Argon2.hPrime (ol s₀) I := by
  have hpos := hp.ol_pos
  have hV : (digest s₀ s).length = 64 := by simp [digest, bytesAt]
  unfold finishOutput
  refine WP.seq ((cmp_ok hp b o).mono fun s₁ ⟨cf₁, k₁, m₁⟩ => ?_)
  simp only [List.length_nil, Nat.sub_zero] at cf₁
  have b₁ := b.keeps hp k₁
  have o₁ := o.keeps hp k₁
  have d₁ : digest s₀ s₁ = digest s₀ s := by show bytesAt _ _ _ = _; rw [m₁]
  have hIte : WP isa (.ite .b (.block []) extendDigest) s₁ fun t => Body s₀ t ∧ t.gpr .ebp = s.gpr .ebp ∧
      ∃ xs, Out s₀ t xs ∧ xs.length < ol s₀ ∧ ol s₀ - xs.length ≤ 64 ∧
        xs ++ (digest s₀ t).take (ol s₀ - xs.length) = Spec.Argon2.hPrime (ol s₀) I := by
    refine WP.ite (decide (ol s₀ < 65)) cf₁ (fun h => WP.block_nil ?_) (fun h => ?_)
    · simp only [decide_eq_true_eq] at h
      refine ⟨b₁, k₁.ebp, [], o₁, by simp only [List.length_nil]; omega,
        by simp only [List.length_nil]; omega, ?_⟩
      rw [Nat.min_eq_left (by omega)] at hd
      rw [List.nil_append, List.length_nil, Nat.sub_zero, d₁, hd]
      simp only [Spec.Argon2.hPrime, eq_true (by omega : ol s₀ ≤ 64), ite_true]
    · simp only [decide_eq_false_iff_not] at h
      refine (extend_ok hp b₁ o₁ (by omega)).mono fun t ⟨j, bt, et, ot, dt, l₁, l₂, l₃⟩ =>
        ⟨bt, et.trans k₁.ebp, _, ot, ?_, ?_, ?_⟩
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega
      · rw [chainOut_length (by rw [d₁]; exact hV)]; omega
      · have V₁ : digest s₀ s₁ = Spec.Argon2.H 64 (Spec.Argon2.le32 (ol s₀) ++ I) := by
          rw [d₁, ← List.take_of_length_le (l := digest s₀ s) (i := 64) (by rw [hV]),
            ← Nat.min_eq_right (by omega : 64 ≤ ol s₀), hd]
        rw [chainOut_length (by rw [d₁]; exact hV), dt, chainOut, ← Proof.Argon2.longHash_chain, V₁]
        have hr : (ol s₀ + 31) / 32 - 2 = j + 1 := by omega
        simp only [Spec.Argon2.hPrime, eq_false (by omega : ¬ ol s₀ ≤ 64), ite_false]
        rw [hr, show ol s₀ - 32 * (j + 1) = ol s₀ - (32 + 32 * j) by omega]
  refine WP.seq (hIte.mono fun s₂ ⟨b₂, e₂, xs, o₂, l₁, l₂, h₂⟩ => ?_)
  refine (copyRemaining_ok hp b₂ o₂ l₁ l₂).mono fun t ⟨bt, et, ht⟩ => ⟨bt, et.trans e₂, ?_⟩
  rw [ht, h₂]

end

end VG.Proof.Argon2.X86.HPrime
