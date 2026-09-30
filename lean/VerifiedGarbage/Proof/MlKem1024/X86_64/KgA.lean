import VerifiedGarbage.Proof.MlKem1024.X86_64.KgBase
import VerifiedGarbage.Proof.MlKem.X86_64.FragS4

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_keygen`, `G` and the matrix

Untrusted: everything here is checked by Lean. `(ρ, σ) = G(d ‖ 4)` to `G`,
and `ρ` to `SB` (`gRho_ok`); then `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the
sixteen entries `e = 4i + j` (`samples_ok`), four at a time with
`vg_mlkem_sample_ntt4` (`quad_step`), with `r15` the AND of the results: 1
exactly when all of them succeed within 280 iterations (`allOk4`).
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The first `e` entries of the 4 × 4 matrix `Â` sampled within 280 iterations. -/
def allOk4 (ρ : List Byte) (e : Nat) : Prop :=
  ∀ e' < e, (sampleNTT minIterations (matSeed ρ (e' / 4) (e' % 4))).isSome

instance (ρ : List Byte) (e : Nat) : Decidable (allOk4 ρ e) := by unfold allOk4; infer_instance

theorem allOk4_add4 {ρ : List Byte} {e : Nat} :
    allOk4 ρ (e + 4) ↔ allOk4 ρ e ∧ ((List.range 4).all fun k =>
      (sampleNTT minIterations (matSeed ρ ((e + k) / 4) ((e + k) % 4))).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), fun k hk => h (e + k) (by omega)⟩
  · rintro ⟨h, h4⟩ e' he
    rcases (by omega : e' < e ∨ e ≤ e') with he' | he'
    · exact h e' he'
    · have := h4 (e' - e) (by omega)
      rwa [Nat.add_sub_cancel' he'] at this

theorem aHat4_eq {ρ : List Byte} (h : allOk4 ρ 16) {i j : Nat} (hi : i < 4) (hj : j < 4) :
    sampleNTT minIterations (matSeed ρ i j) = some (aHat ρ i j) := by
  have := h (4 * i + j) (by omega)
  rw [show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega] at this
  unfold aHat
  cases e : sampleNTT minIterations (matSeed ρ i j) with
  | none => rw [e] at this; cases this
  | some f => rfl

theorem not_allOk4 {ρ : List Byte} (h : ¬ allOk4 ρ 16) :
    ∃ i < 4, ∃ j < 4, sampleNTT minIterations (matSeed ρ i j) = none := by
  unfold allOk4 at h
  simp only [Classical.not_forall] at h
  obtain ⟨e, he, hs⟩ := h
  refine ⟨e / 4, by omega, e % 4, by omega, ?_⟩
  cases e' : sampleNTT minIterations (matSeed ρ (e / 4) (e % 4)) with
  | none => rfl
  | some f => rw [e'] at hs; exact absurd rfl hs

namespace KeyGen4

open VG.Impl.MlKem1024.X86_64.KeyGen1024

/-! ## `G(d ‖ 4)` -/

/-- After `G`: `ρ` and `σ` at `G`, and `ρ` at `SB`. -/
structure KA (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = kgRho1024 (kgD σ)
  sig : bytesAt s.mem (pa s sigP) 32 = kgSigma1024 (kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = kgRho1024 (kgD σ)

theorem gRho_ok {σ : State} (hp : keyGen1024K.pre σ) {s : State} (h : KC σ s) (h15 : s.gpr .r15 = 1) :
    WP isa gRho s fun s' => KA σ s' ∧ s'.gpr .r15 = 1 := by
  have L := h.lay hp
  unfold gRho
  refine WP.seq (WP.mono (setB_okL L (by decide) (by decide) (p := sc oNB) (v := 4) (by decide))
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.step hp hP₁.b (by decide)
  have L₁ := h₁.lay hp
  refine WP.seq (WP.mono (hash_ok kgB_bases (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
    (len := 64) (by decide) (show 6 < 256 by decide) L₁) fun s₂ ⟨hP₂, ho₂⟩ => ?_)
  have h₂ := h₁.step hp hP₂.b (by decide)
  have L₂ := h₂.lay hp
  refine WP.mono (copy_okL L₂ (dst := sc oSB) (src := sc oG) (n := 32) (by decide) (by decide))
    fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have h₃ := h₂.step hp hP₃.b (by decide)
  -- The output of `G`.
  have hpc : pieces s₁ [((.rbp, 0), 32), (sc oNB, 1)] = kgD σ ++ [BitVec.ofNat 8 4] := by
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h₁.d]
    rw [show pa s₁ (sc oNB) = pa s (sc oNB) from hP₁.pa rbx_cs, hb₁]
  rw [hpc, KeyGen.sha3Suffix6, ← sha3_512_eq] at ho₂
  have eG : pa s₂ (sc oG) = pa s₁ (sc oG) := hP₂.pa rbx_cs
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (kgD σ ++ [BitVec.ofNat 8 4]) := by
    rw [eG]; exact ho₂
  have hρ : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = kgRho1024 (kgD σ) := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hσ : bytesAt s₂.mem (pa s₂ sigP) 32 = kgSigma1024 (kgD σ) := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨h₃, ?_, ?_, ?_⟩, ?_⟩
  · rw [L₂.keepBytes hP₃.b (by decide)]; exact hρ
  · rw [L₂.keepBytes hP₃.b (by decide)]; exact hσ
  · rw [show pa s₃ (sc oSB) = pa s₂ (sc oSB) from hP₃.pa rbx_cs, hb₃, hρ]
  · rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]

/-! ## The matrix -/

/-- After the first `e` entries of `Â`. -/
structure KB (e : Nat) (σ s : State) : Prop where
  a : KA σ s
  r15 : s.gpr .r15 = if allOk4 (kgRho1024 (kgD σ)) e then 1 else 0
  mat : ∀ e' < e, ∀ f, sampleNTT minIterations (matSeed (kgRho1024 (kgD σ)) (e' / 4) (e' % 4)) = some f →
    PolyIs s.mem (pa s (aS4 (e' / 4) (e' % 4))) f

/-- What entries `e, …, e + 3` of `Â` write. -/
abbrev qW4 (e : Nat) : List (Ptr × Nat) := quadW (oP (17 + e)) (oP 35)

def kqChk (e : Nat) : Bool :=
  quadChk kgB kgW (oP (17 + e)) (oP 35) && kcChk (qW4 e) && keepB kgB (qW4 e) (sc oG) 32 &&
    keepB kgB (qW4 e) sigP 32 && keepB kgB (qW4 e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB kgB (qW4 e) (aS4 (e' / 4) (e' % 4)) 1024

theorem kqChk_all : kqChk 0 = true ∧ kqChk 4 = true ∧ kqChk 8 = true ∧ kqChk 12 = true := by decide

/-- Entry `e` of `Â`, as polynomial `17 + e`. -/
theorem aS4_eq (e : Nat) : aS4 (e / 4) (e % 4) = sc (oP (17 + e)) := by
  simp only [aS4, pS, oP]
  congr 1
  omega

theorem KB.zero {σ s : State} (h : KA σ s) (h15 : s.gpr .r15 = 1) : KB 0 σ s :=
  ⟨h, by rw [h15, ifp (show allOk4 (kgRho1024 (kgD σ)) 0 from fun _ h => absurd h (Nat.not_lt_zero _))],
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem quad_step (v : Sample4Impl) {σ : State} (hp : keyGen1024K.pre σ) {e : Nat} (hc : kqChk e = true)
    (he : e + 4 ≤ 16) {s : State} (h : KB e σ s) :
    WP isa (quad v.callee 4 e (sc (oP (17 + e))) (pS 35)) s (KB (e + 4) σ) := by
  simp only [kqChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hq, hkc⟩, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  have L := h.a.kc.lay hp
  refine WP.mono (quad_ok v L kgB_bases (by omega) hq) fun s' ⟨hP, h15, hres⟩ => ?_
  refine ⟨⟨h.a.kc.step hp hP hkc, by rw [L.keepBytes hP kG]; exact h.a.rho, by rw [L.keepBytes hP kS]; exact h.a.sig,
    by rw [L.keepBytes hP kB]; exact h.a.sb⟩, ?_, fun e' he' f hf => ?_⟩
  · rw [h15, h.a.sb, and_acc h.r15]
    exact ite_congr (propext allOk4_add4.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact L.keepPoly hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [h.a.sb, Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases, aS4_eq]
      rwa [show oP (17 + e) + 1024 * (e' - e) = oP (17 + e') by simp only [oP]; omega] at this

theorem samples_ok (v : Sample4Impl) {σ : State} (hp : keyGen1024K.pre σ) {s : State} (h : KB 0 σ s) :
    WP isa (samples4 v.callee) s (KB 16 σ) :=
  WP.seq (WP.mono (quad_step v hp kqChk_all.1 (by decide) h) fun _ h₁ =>
    WP.seq (WP.mono (quad_step v hp kqChk_all.2.1 (by decide) h₁) fun _ h₂ =>
      WP.seq (WP.mono (quad_step v hp kqChk_all.2.2.1 (by decide) h₂) fun _ h₃ =>
        quad_step v hp kqChk_all.2.2.2 (by decide) h₃)))

end KeyGen4

end VG.Proof.MlKem1024.X86_64
