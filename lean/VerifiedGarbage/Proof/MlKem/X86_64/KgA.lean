import VerifiedGarbage.Proof.MlKem.X86_64.KgBase
import VerifiedGarbage.Proof.MlKem.X86_64.FragS4

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_keygen`, `G` and the matrix

Untrusted: everything here is checked by Lean. `(ρ, σ) = G(d ‖ 3)` to `G`,
and `ρ` to `SB` (`gRho_ok`); then `Â[i, j] = SampleNTT(ρ ‖ j ‖ i)` for the
nine entries `e = 3i + j` (`samples_ok`), four at a time with
`vg_mlkem_sample_ntt4` (`quad_step`) and the last on its own, with `r15` the
AND of the results: 1 exactly when all of them succeed within 280
iterations (`allOk`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- The first `e` entries of `Â` sampled within 280 iterations. -/
def allOk (ρ : List Byte) (e : Nat) : Prop :=
  ∀ e' < e, (sampleNTT minIterations (matSeed ρ (e' / 3) (e' % 3))).isSome

instance (ρ : List Byte) (e : Nat) : Decidable (allOk ρ e) := by unfold allOk; infer_instance

theorem allOk_succ {ρ : List Byte} {e : Nat} :
    allOk ρ (e + 1) ↔ allOk ρ e ∧ (sampleNTT minIterations (matSeed ρ (e / 3) (e % 3))).isSome := by
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), h e (by omega)⟩
  · rintro ⟨h, hk⟩ e' he
    rcases (by omega : e' < e ∨ e' = e) with he | rfl
    · exact h e' he
    · exact hk

theorem allOk_add4 {ρ : List Byte} {e : Nat} :
    allOk ρ (e + 4) ↔ allOk ρ e ∧ ((List.range 4).all fun k =>
      (sampleNTT minIterations (matSeed ρ ((e + k) / 3) ((e + k) % 3))).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), fun k hk => h (e + k) (by omega)⟩
  · rintro ⟨h, h4⟩ e' he
    rcases (by omega : e' < e ∨ e ≤ e') with he' | he'
    · exact h e' he'
    · have := h4 (e' - e) (by omega)
      rwa [Nat.add_sub_cancel' he'] at this

/-- `r15` after one more `SampleNTT`. -/
theorem and_acc {r : BitVec 64} {p q : Prop} [Decidable p] [Decidable q] (hr : r = if p then 1 else 0) :
    BitVec.setWidth 64 (r.setWidth 32 &&& (if q then 1 else 0)) = if p ∧ q then 1 else 0 := by
  subst hr
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- `Â[i, j]`, if its `SampleNTT` succeeds. -/
def aHat (ρ : List Byte) (i j : Nat) : Poly := (sampleNTT minIterations (matSeed ρ i j)).getD zero

theorem aHat_eq {ρ : List Byte} (h : allOk ρ 9) {i j : Nat} (hi : i < 3) (hj : j < 3) :
    sampleNTT minIterations (matSeed ρ i j) = some (aHat ρ i j) := by
  have := h (3 * i + j) (by omega)
  rw [show (3 * i + j) / 3 = i by omega, show (3 * i + j) % 3 = j by omega] at this
  unfold aHat
  cases e : sampleNTT minIterations (matSeed ρ i j) with
  | none => rw [e] at this; cases this
  | some f => rfl

theorem not_allOk {ρ : List Byte} (h : ¬ allOk ρ 9) :
    ∃ i < 3, ∃ j < 3, sampleNTT minIterations (matSeed ρ i j) = none := by
  unfold allOk at h
  simp only [Classical.not_forall] at h
  obtain ⟨e, he, hs⟩ := h
  refine ⟨e / 3, by omega, e % 3, by omega, ?_⟩
  cases e' : sampleNTT minIterations (matSeed ρ (e / 3) (e % 3)) with
  | none => rfl
  | some f => rw [e'] at hs; exact absurd rfl hs

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-! ## `G(d ‖ 3)` -/

theorem sha3Suffix6 : BitVec.ofNat 8 6 = Spec.Sha3.sha3Suffix := by decide

/-- After `G`: `ρ` and `σ` at `G`, and `ρ` at `SB`. -/
structure KA (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = kgRho (kgD σ)
  sig : bytesAt s.mem (pa s sigP) 32 = kgSigma (kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = kgRho (kgD σ)

theorem gRho_ok {σ : State} (hp : keyGenK.pre σ) {s : State} (h : KC σ s) (h15 : s.gpr .r15 = 1) :
    WP isa gRho s fun s' => KA σ s' ∧ s'.gpr .r15 = 1 := by
  have L := h.lay hp
  unfold gRho
  refine WP.seq (WP.mono (setB_okL L (by decide) (by decide) (p := sc oNB) (v := 3) (by decide))
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
  have hpc : pieces s₁ [((.rbp, 0), 32), (sc oNB, 1)] = kgD σ ++ [BitVec.ofNat 8 3] := by
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h₁.d]
    rw [show pa s₁ (sc oNB) = pa s (sc oNB) from hP₁.pa rbx_cs, hb₁]
  rw [hpc, sha3Suffix6, ← sha3_512_eq] at ho₂
  have eG : pa s₂ (sc oG) = pa s₁ (sc oG) := hP₂.pa rbx_cs
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (kgD σ ++ [BitVec.ofNat 8 3]) := by
    rw [eG]; exact ho₂
  have hρ : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = kgRho (kgD σ) := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hσ : bytesAt s₂.mem (pa s₂ sigP) 32 = kgSigma (kgD σ) := by
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
  r15 : s.gpr .r15 = if allOk (kgRho (kgD σ)) e then 1 else 0
  mat : ∀ e' < e, ∀ f, sampleNTT minIterations (matSeed (kgRho (kgD σ)) (e' / 3) (e' % 3)) = some f →
    PolyIs s.mem (pa s (aS (e' / 3) (e' % 3))) f

/-- What entry `e` of `Â` writes. -/
abbrev ijW (e : Nat) : List (Ptr × Nat) :=
  [(sc (oSB + 32), 1)] ++ [(sc (oSB + 33), 1)] ++ [(aS (e / 3) (e % 3), 1024), (sc oSS, 2048)]

def kbChk (e : Nat) : Bool :=
  ijChk kgB kgW (aS (e / 3) (e % 3)) && kcChk (ijW e) && keepB kgB (ijW e) (sc oG) 32 &&
    keepB kgB (ijW e) sigP 32 && keepB kgB (ijW e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB kgB (ijW e) (aS (e' / 3) (e' % 3)) 1024

theorem kbChk_all : ∀ e < 9, kbChk e = true := by decide

theorem KB.zero {σ s : State} (h : KA σ s) (h15 : s.gpr .r15 = 1) : KB 0 σ s :=
  ⟨h, by rw [h15, ifp (show allOk (kgRho (kgD σ)) 0 from fun _ h => absurd h (Nat.not_lt_zero _))],
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem sample_step {σ : State} (hp : keyGenK.pre σ) {e : Nat} (he : e < 9) {s : State} (h : KB e σ s) :
    WP isa (sampleIJ (e / 3) (e % 3)) s (KB (e + 1) σ) := by
  have hc := kbChk_all e he
  simp only [kbChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hij, hkc⟩, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  have L := h.a.kc.lay hp
  refine WP.mono (sampleIJ_ok L kgB_bases (by omega) (by omega) hij) fun s' ⟨hP, h15, hres⟩ => ?_
  refine ⟨⟨h.a.kc.step hp hP hkc, by rw [L.keepBytes hP kG]; exact h.a.rho, by rw [L.keepBytes hP kS]; exact h.a.sig,
    by rw [L.keepBytes hP kB]; exact h.a.sb⟩, ?_, fun e' he' f hf => ?_⟩
  · rw [h15, h.a.sb, and_acc h.r15]
    exact ite_congr (propext allOk_succ.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · exact L.keepPoly hP (kA e' he') (h.mat e' he' f hf)
    · rw [hP.pa rbx_bases]
      exact hres f (by rw [h.a.sb]; exact hf)

/-- What entries `e, …, e + 3` of `Â` write. -/
abbrev qW (e : Nat) : List (Ptr × Nat) := quadW (oP (6 + e)) (oP 17)

def kqChk (e : Nat) : Bool :=
  quadChk kgB kgW (oP (6 + e)) (oP 17) && kcChk (qW e) && keepB kgB (qW e) (sc oG) 32 &&
    keepB kgB (qW e) sigP 32 && keepB kgB (qW e) (sc oSB) 32 &&
    (List.range e).all fun e' => keepB kgB (qW e) (aS (e' / 3) (e' % 3)) 1024

theorem kqChk_all : kqChk 0 = true ∧ kqChk 4 = true := by decide

/-- Entry `e` of `Â`, as polynomial `6 + e`. -/
theorem aS_eq (e : Nat) : aS (e / 3) (e % 3) = sc (oP (6 + e)) := by
  simp only [aS, pS, oP]
  congr 1
  omega

theorem quad_step (v : Sample4Impl) {σ : State} (hp : keyGenK.pre σ) {e : Nat} (hc : kqChk e = true)
    (he : e + 4 ≤ 9) {s : State} (h : KB e σ s) :
    WP isa (quad v.callee 3 e (sc (oP (6 + e))) (pS 17)) s (KB (e + 4) σ) := by
  simp only [kqChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hq, hkc⟩, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  have L := h.a.kc.lay hp
  refine WP.mono (quad_ok v L kgB_bases (by omega) hq) fun s' ⟨hP, h15, hres⟩ => ?_
  refine ⟨⟨h.a.kc.step hp hP hkc, by rw [L.keepBytes hP kG]; exact h.a.rho, by rw [L.keepBytes hP kS]; exact h.a.sig,
    by rw [L.keepBytes hP kB]; exact h.a.sb⟩, ?_, fun e' he' f hf => ?_⟩
  · rw [h15, h.a.sb, and_acc h.r15]
    exact ite_congr (propext allOk_add4.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact L.keepPoly hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [h.a.sb, Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases, aS_eq]
      rwa [show oP (6 + e) + 1024 * (e' - e) = oP (6 + e') by simp only [oP]; omega] at this

theorem samples_ok (v : Sample4Impl) {σ : State} (hp : keyGenK.pre σ) {s : State} (h : KB 0 σ s) :
    WP isa (samples v.callee) s (KB 9 σ) :=
  WP.seq (WP.mono (quad_step v hp kqChk_all.1 (by decide) h) fun _ h₁ =>
    WP.seq (WP.mono (quad_step v hp kqChk_all.2 (by decide) h₁) fun _ h₂ => sample_step hp (by decide) h₂))

end KeyGen

end VG.Proof.MlKem.X86_64
