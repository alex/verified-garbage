import VerifiedGarbage.Proof.MlKem1024.AArch64.KgC

/-!
# ML-KEM-1024 on AArch64: `vg_mlkem1024_keygen`, `ŝ` and `t̂`

`ŝ[j]` and its encoding into `dk` (`s_step`), then `ê[i]` and `t̂[i]` and its
encodings into `ek` and `dk` (`t_step`), each keeping what the steps before
established (`CInv`).
-/

namespace VG.Proof.MlKem1024.AArch64.KeyGen

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlKem1024.AArch64 VG.Impl.MlKem1024.AArch64.KG VG.Proof.MlKem
  VG.Proof.MlKem.AArch64 VG.Proof.MlKem1024 VG.Proof.MlKem1024.AArch64
open VG.Impl.MlKem.AArch64 (mov ptrTo Piece hash hashWith copy32)
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt Repr)

/-- `Â[e]`'s buffer. -/
abbrev AR (s₀ : State) (e : Nat) : Addr := kA s₀ 3 + BitVec.ofNat 64 (AH + 1024 * e)

/-- What phase C keeps: `ρ`, `σ`, `x24`, and `Â` as the matrix left it
(in `mB`). -/
structure CInv (s₀ : State) (mB : Mem) (v : BitVec 64) (s : State) : Prop where
  kb : KB s₀ s
  rho : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SB) 32 = rhoK s₀
  sig : bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 SG) 32 = kgSigma1024 (dB s₀)
  x24 : s.gpr .x24 = v
  ahat : ∀ e < 16, Reduced s.mem (AR s₀ e) ∧ polyAt s.mem (AR s₀ e) = polyAt mB (AR s₀ e)

/-- Memory changed only in `W`, which is apart from `ρ`, `σ` and `Â`. -/
theorem CInv.frame {s₀ : State} {mB : Mem} {v : BitVec 64} {s s' : State} (h : CInv s₀ mB v s)
    (hk : KB s₀ s') (hx : s'.gpr .x24 = s.gpr .x24) {W : List Region} (hf : Frame W s.mem s'.mem)
    (hW : ∀ r ∈ W, (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH 16384).Disjoint r) : CInv s₀ mB v s' := by
  have ha : ∀ e < 16, ∀ r ∈ W, (polyRegion (AR s₀ e)).Disjoint r := fun e he r hr =>
    (hW r hr).2.2.sub_left (by
      rw [show AR s₀ e = kA s₀ 3 + BitVec.ofNat 64 AH + BitVec.ofNat 64 (1024 * e) by rw [ptr_add]]
      exact sub_offset' (by omega))
  refine ⟨hk, ?_, ?_, by rw [hx, h.x24], fun e he => ⟨reduced_frame hf (ha e he) (h.ahat e he).1, ?_⟩⟩
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).1) (by decide)]; exact h.rho
  · rw [bytesAt_frame hf (fun r hr => (hW r hr).2.1) (by decide)]; exact h.sig
  · rw [polyAt_frame hf (ha e he)]; exact (h.ahat e he).2

/-- A buffer apart from everything `(kgCbdNttWith keccak.callee)` writes. -/
theorem cnW_apart {s₀ : State} (hp : Pre s₀) {off b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b)
    (h : b ≠ 3 ∨ (840 ≤ o ∧ (o + l ≤ 912 ∨ 913 ≤ o) ∧ (o + l ≤ 928 ∨ 1056 ≤ o) ∧
      (o + l ≤ off ∨ off + 1024 ≤ o) ∧ (o + l ≤ 3104 ∨ 4128 ≤ o))) (ho : off + 1024 ≤ kL 3) :
    ∀ r ∈ cnW s₀ off, (R (kA s₀) b o l).Disjoint r := by
  intro r hr
  rcases mem7 hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine hp.args.rdisj hb (by decide) f (by decide) ?_; simp only [KG.ST]; omega
  · refine hp.args.rdisj hb (by decide) f (by decide) ?_; simp only [KG.WK]; omega
  · exact below_R hp hb f
  · refine hp.args.rdisj hb (by decide) f (by decide) ?_; simp only [KG.SG]; omega
  · refine hp.args.rdisj hb (by decide) f (by decide) ?_; simp only [KG.PB]; omega
  · refine hp.args.rdisj hb (by decide) f ho ?_; omega
  · refine hp.args.rdisj hb (by decide) f (by decide) ?_; simp only [KG.NS]; omega

/-- `ρ`, `σ` and `Â` are apart from what `(kgCbdNttWith keccak.callee)` writes, for a polynomial past `Â`. -/
theorem cnW_far {s₀ : State} (hp : Pre s₀) {off : Nat} (ho : SH ≤ off ∧ off + 1024 ≤ SV) :
    ∀ r ∈ cnW s₀ off, (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH 16384).Disjoint r := by
  simp only [SH, SV] at ho
  have hoL : off + 1024 ≤ kL 3 := by simp only [kL]; omega
  intro r hr
  exact ⟨cnW_apart hp (by decide) (by decide) (.inr (by offs4; omega)) hoL r hr,
    cnW_apart hp (by decide) (by decide) (.inr (by offs4; omega)) hoL r hr,
    cnW_apart hp (by decide) (by decide) (.inr (by offs4; omega)) hoL r hr⟩

/-- A single buffer of `ek`, `dk` or past `Â` in `scratch` is apart from `ρ`, `σ` and `Â`. -/
theorem one_far {s₀ : State} (hp : Pre s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL b)
    (h : b ≠ 3 ∨ SH ≤ o) :
    ∀ r ∈ [R (kA s₀) b o l], (R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
      (R (kA s₀) 3 AH 16384).Disjoint r := by
  intro r hr
  rw [List.mem_singleton.mp hr]
  simp only [SH] at h
  exact ⟨hp.args.rdisj (by decide) hb (by decide) f (by simp only [SB]; omega),
    hp.args.rdisj (by decide) hb (by decide) f (by simp only [SG]; omega),
    hp.args.rdisj (by decide) hb (by decide) f (by simp only [AH]; omega)⟩

/-- After `ŝ[j']` for `j' < j`. -/
structure SInv (s₀ : State) (mB : Mem) (v : BitVec 64) (j : Nat) (s : State) : Prop where
  c : CInv s₀ mB v s
  sp : ∀ j' < j, PolyIs s.mem (kA s₀ 3 + BitVec.ofNat 64 (sOff j')) (kgS1024 (dB s₀) j')
  dk : ∀ j' < j, bytesAt s.mem (kA s₀ 2 + BitVec.ofNat 64 (384 * j')) 384 = encode12 (kgS1024 (dB s₀) j')

theorem s_step {s₀ : State} (hp : Pre s₀) {mB : Mem} {v : BitVec 64} {j : Nat} (hj : j < 4) {s : State}
    (h : SInv s₀ mB v j s) : WP isa (Impl.MlKem1024.AArch64.kgSWith keccak.callee j) s (SInv s₀ mB v (j + 1)) := by
  have hj' : SH + 1024 * j + 1024 ≤ SV := by simp only [SH, SV]; omega
  have hpo : PolyOff (sOff j) := ⟨by simp only [sOff, SH, AH]; omega, hj'⟩
  have hoL : sOff j + 1024 ≤ kL 3 := by simp only [sOff, SH, kL]; omega
  have fd : 384 * j + 384 ≤ kL 2 := by simp only [kL]; omega
  refine WP.seq (WP.mono (cbdNtt_ok hp (N := j) (off := sOff j) (by omega) hpo h.c.kb h.c.sig)
    fun s₁ ⟨kb₁, f₁, p₁, x₁⟩ => ?_)
  refine WP.mono (enc_ok hp (off := sOff j) (b := 2) (o := 384 * j) hpo (.inr rfl) fd kb₁ p₁.1)
    fun s₂ ⟨kb₂, f₂, b₂, x₂⟩ => ?_
  have c₂ := (h.c.frame kb₁ x₁ f₁ (cnW_far hp ⟨by simp only [sOff]; omega, hj'⟩)).frame kb₂ x₂ f₂
    (one_far hp (by decide) fd (.inl (by decide)))
  refine ⟨c₂, fun j' hj' => ?_, fun j' hj' => ?_⟩
  · have hS : ∀ r ∈ [R (kA s₀) 2 (384 * j) 384], (R (kA s₀) 3 (sOff j') 1024).Disjoint r := fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact hp.args.rdisj (by decide) (by decide) (by simp only [sOff, SH, kL]; omega) fd (.inl (by decide))
    rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
    · refine polyIs_frame f₂ hS (polyIs_frame f₁ (cnW_apart hp (by decide)
        (by simp only [sOff, SH, kL]; omega) (.inr (by offs4; omega)) hoL)
        (h.sp j' hj'))
    · exact polyIs_frame f₂ hS p₁
  · rcases (by omega : j' < j ∨ j' = j) with hj' | rfl
    · rw [bytesAt_frame f₂ (fun r hr => by
          rw [List.mem_singleton.mp hr]
          exact hp.args.rdisj (by decide) (by decide) (by simp only [kL]; omega) fd (by omega))
          (by decide),
        bytesAt_frame f₁ (cnW_apart hp (by decide) (by simp only [kL]; omega) (.inl (by decide)) hoL)
          (by decide)]
      exact h.dk j' hj'
    · rw [b₂, p₁.2, kgS1024, KPke.kgS]

end VG.Proof.MlKem1024.AArch64.KeyGen
