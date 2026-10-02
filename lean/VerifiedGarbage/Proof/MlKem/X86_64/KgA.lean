import VerifiedGarbage.Proof.MlKem.X86_64.KgBase
import VerifiedGarbage.Proof.MlKem.X86_64.FragS4

/-!
# ML-KEM on x86-64: key generation, `G` and the matrix

`(ρ, σ) = G(d ‖ k)` to `G`, and `ρ` to `SB` (`gRho_ok`); then `Â[i, j] =
SampleNTT(ρ ‖ j ‖ i)` for the `k²` entries `e = k i + j` (`samples_ok`), four
at a time with `vg_mlkem_sample_ntt4` (`quad_step`) and the last `k² mod 4`
on their own (`sample_step`), with `r15` the AND of the results: 1 exactly
when all of them succeed within 280 iterations (`allOk`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- Entry `e = k i + j` of a `k × k` matrix is `(i, j)`. -/
theorem divmod_ij {k i j : Nat} (hj : j < k) : (k * i + j) / k = i ∧ (k * i + j) % k = j :=
  ⟨by rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero],
    by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]⟩

theorem ij_lt {k i j : Nat} (hi : i < k) (hj : j < k) : k * i + j < k * k :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi)

theorem div_lt_k {k e : Nat} (he : e < k * k) : e / k < k := Nat.div_lt_of_lt_mul he

theorem mod_lt_k {k e : Nat} (he : e < k * k) : e % k < k := Nat.mod_lt _ (Nat.pos_of_ne_zero fun h => by
  subst h; exact absurd he (Nat.not_lt_zero _))

/-- The first `e` entries of `Â` (`k × k`) sampled within 280 iterations. -/
def allOk (k : Nat) (ρ : List Byte) (e : Nat) : Prop :=
  ∀ e' < e, (sampleNTT minIterations (matSeed ρ (e' / k) (e' % k))).isSome

instance (k : Nat) (ρ : List Byte) (e : Nat) : Decidable (allOk k ρ e) := by unfold allOk; infer_instance

theorem allOk_succ {k : Nat} {ρ : List Byte} {e : Nat} :
    allOk k ρ (e + 1) ↔ allOk k ρ e ∧ (sampleNTT minIterations (matSeed ρ (e / k) (e % k))).isSome := by
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), h e (by omega)⟩
  · rintro ⟨h, hk⟩ e' he
    rcases (by omega : e' < e ∨ e' = e) with he | rfl
    · exact h e' he
    · exact hk

theorem allOk_add4 {k : Nat} {ρ : List Byte} {e : Nat} :
    allOk k ρ (e + 4) ↔ allOk k ρ e ∧ ((List.range 4).all fun t =>
      (sampleNTT minIterations (matSeed ρ ((e + t) / k) ((e + t) % k))).isSome) = true := by
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h; exact ⟨fun e' he => h e' (by omega), fun t ht => h (e + t) (by omega)⟩
  · rintro ⟨h, h4⟩ e' he
    rcases (by omega : e' < e ∨ e ≤ e') with he' | he'
    · exact h e' he'
    · have := h4 (e' - e) (by omega)
      rwa [Nat.add_sub_cancel' he'] at this

theorem allOk_zero (k : Nat) (ρ : List Byte) : allOk k ρ 0 := fun _ h => absurd h (Nat.not_lt_zero _)

/-- `r15` after one more `SampleNTT`. -/
theorem and_acc {r : BitVec 64} {p q : Prop} [Decidable p] [Decidable q] (hr : r = if p then 1 else 0) :
    BitVec.setWidth 64 (r.setWidth 32 &&& (if q then 1 else 0)) = if p ∧ q then 1 else 0 := by
  subst hr
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- `Â[i, j]`, if its `SampleNTT` succeeds. -/
def aHat (ρ : List Byte) (i j : Nat) : Poly := (sampleNTT minIterations (matSeed ρ i j)).getD zero

theorem aHat_eq {k : Nat} {ρ : List Byte} (h : allOk k ρ (k * k)) {i j : Nat} (hi : i < k) (hj : j < k) :
    sampleNTT minIterations (matSeed ρ i j) = some (aHat ρ i j) := by
  have := h (k * i + j) (ij_lt hi hj)
  rw [(divmod_ij hj).1, (divmod_ij hj).2] at this
  unfold aHat
  cases e : sampleNTT minIterations (matSeed ρ i j) with
  | none => rw [e] at this; cases this
  | some f => rfl

theorem not_allOk {k : Nat} {ρ : List Byte} (h : ¬ allOk k ρ (k * k)) :
    ∃ i < k, ∃ j < k, sampleNTT minIterations (matSeed ρ i j) = none := by
  unfold allOk at h
  simp only [Classical.not_forall] at h
  obtain ⟨e, he, hs⟩ := h
  refine ⟨e / k, div_lt_k he, e % k, mod_lt_k he, ?_⟩
  cases e' : sampleNTT minIterations (matSeed ρ (e / k) (e % k)) with
  | none => rfl
  | some f => rw [e'] at hs; exact absurd rfl hs

/-- Entry `e` of `Â` (`k × k`), as polynomial `pA + e`. -/
theorem aS_eq (L : Kem) (e : Nat) : L.aS (e / L.k) (e % L.k) = pS (L.pA + e) := by
  rw [Kem.aS, Nat.add_assoc, Nat.div_add_mod]

theorem aS_ij (L : Kem) (i j : Nat) : L.aS i j = pS (L.pA + (L.k * i + j)) := by
  rw [Kem.aS, Nat.add_assoc]

/-! ## Sampling the matrix, for any layout -/

/-- After the first `e` entries of `Â` (`k × k`, from polynomial `pA`): `r15`,
and the entries sampled, for the seed `ρ`. -/
structure MatB (L : Kem) (ρ : List Byte) (e : Nat) (s : State) : Prop where
  r15 : s.gpr .r15 = if allOk L.k ρ e then 1 else 0
  mat : ∀ e' < e, ∀ f, sampleNTT minIterations (matSeed ρ (e' / L.k) (e' % L.k)) = some f →
    PolyIs s.mem (pa s (pS (L.pA + e'))) f

/-- The step of one entry. -/
theorem MatB.single {L : Kem} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB L ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (pS (L.pA + e')) 1024 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / L.k) (e % L.k))).isSome
          then 1 else 0)))
    (hres : ∀ f, sampleNTT minIterations (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) (e / L.k) (e % L.k)) = some f →
        PolyIs s'.mem (pa s (pS (L.pA + e))) f) : MatB L ρ (e + 1) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, and_acc h.r15]
    exact ite_congr (propext allOk_succ.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e' = e) with he' | rfl
    · exact Lx.keepPoly hP (kA e' he') (h.mat e' he' f hf)
    · rw [hP.pa rbx_bases]
      exact hres f (by rw [hsb]; exact hf)

/-- The step of four entries. -/
theorem MatB.four {L : Kem} {ρ : List Byte} {e : Nat} {rbs wbs : List (Reg × Nat)} {s s' : State}
    (h : MatB L ρ e s) (hsb : bytesAt s.mem (pa s (sc oSB)) 32 = ρ) (Lx : Lay rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws)
    (kA : ∀ e' < e, keepB (rbs ++ wbs) ws (pS (L.pA + e')) 1024 = true)
    (h15 : s'.gpr .r15 = BitVec.setWidth 64 ((s.gpr .r15).setWidth 32 &&&
        (if (List.range 4).all (fun t => (sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / L.k) ((e + t) % L.k))).isSome) then 1 else 0)))
    (hres : ∀ t < 4, ∀ f, sampleNTT minIterations
          (matSeed (bytesAt s.mem (pa s (sc oSB)) 32) ((e + t) / L.k) ((e + t) % L.k)) = some f →
        PolyIs s'.mem (pa s (sc (oP (L.pA + e) + 1024 * t))) f) : MatB L ρ (e + 4) s' := by
  refine ⟨?_, fun e' he' f hf => ?_⟩
  · rw [h15, hsb, and_acc h.r15]
    exact ite_congr (propext allOk_add4.symm) (fun _ => rfl) (fun _ => rfl)
  · rcases (by omega : e' < e ∨ e ≤ e') with he'' | he''
    · exact Lx.keepPoly hP (kA e' he'') (h.mat e' he'' f hf)
    · have := hres (e' - e) (by omega) f (by rw [hsb, Nat.add_sub_cancel' he'']; exact hf)
      rw [hP.pa rbx_bases]
      rwa [show oP (L.pA + e) + 1024 * (e' - e) = oP (L.pA + e') by simp only [oP]; omega] at this

theorem MatB.zero (L : Kem) (ρ : List Byte) {s : State} (h15 : s.gpr .r15 = 1) : MatB L ρ 0 s :=
  ⟨by rw [h15, ifp (allOk_zero _ _)], fun _ h => absurd h (Nat.not_lt_zero _)⟩

/-- Every entry of `Â`, once all were sampled. -/
theorem MatB.all {L : Kem} {ρ : List Byte} {s : State} (h : MatB L ρ (L.k * L.k) s)
    (ho : allOk L.k ρ (L.k * L.k)) : ∀ i < L.k, ∀ j < L.k, PolyIs s.mem (pa s (L.aS i j)) (aHat ρ i j) :=
  fun i hi j hj => by
    have := h.mat (L.k * i + j) (ij_lt hi hj) (aHat ρ i j)
    rw [(divmod_ij hj).1, (divmod_ij hj).2] at this
    rw [aS_ij L i j]
    exact this (aHat_eq ho hi hj)

/-- The entries `e, …, e + n - 1`, from any invariant `I e` whose steps are
those of one entry and of four (`ents`). -/
theorem ents_ok (L : Kem) (c : Callee4) {I : Nat → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s (I (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, ∀ s, I (4 * q) s →
      WP isa (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) s (I (4 * q + 4))) :
    ∀ n e, e + n = L.k * L.k → (e % 4 = 0 ∨ 4 * (L.k * L.k / 4) ≤ e) → ∀ s, I e s → WP isa (L.ents c e n) s (I (e + n))
  | 0, e, _, _, s, hs => by simp only [Kem.ents]; exact WP.block_nil hs
  | 1, e, he, hq, s, hs => by
    simp only [Kem.ents]; exact h1 e (by omega) (by omega) s hs
  | 2, e, he, hq, s, hs => by
    simp only [Kem.ents]
    exact WP.seq (WP.mono (h1 e (by omega) (by omega) s hs) fun s₁ h₁ =>
      ents_ok L c h1 h4 1 (e + 1) (by omega) (by omega) s₁ h₁)
  | 3, e, he, hq, s, hs => by
    simp only [Kem.ents]
    refine WP.seq (WP.mono (h1 e (by omega) (by omega) s hs) fun s₁ h₁ => ?_)
    have := ents_ok L c h1 h4 2 (e + 1) (by omega) (by omega) s₁ h₁
    rwa [show e + 1 + 2 = e + 3 by omega] at this
  | 4, e, he, hq, s, hs => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega) s (by rwa [show 4 * (e / 4) = e by omega])
    rwa [show 4 * (e / 4) = e by omega] at this
  | n + 5, e, he, hq, s, hs => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega) s (by rwa [show 4 * (e / 4) = e by omega])
    rw [show 4 * (e / 4) = e by omega] at this
    refine WP.seq (WP.mono this fun s₁ h₁ => ?_)
    have := ents_ok L c h1 h4 (n + 1) (e + 4) (by omega) (by omega) s₁ h₁
    rwa [show e + 4 + (n + 1) = e + (n + 5) by omega] at this

theorem samples_ok' (L : Kem) (c : Callee4) {I : Nat → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → ∀ s, I e s →
      WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s (I (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, ∀ s, I (4 * q) s →
      WP isa (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) s (I (4 * q + 4)))
    {s : State} (h : I 0 s) : WP isa (L.samples c) s (I (L.k * L.k)) := by
  have := ents_ok L c h1 h4 (L.k * L.k) 0 (by omega) (by omega) s h
  rwa [Nat.zero_add] at this

/-- `ents_ok`, for constant time. -/
theorem ents_tr (L : Kem) (c : Callee4) {R : Nat → State → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) (R (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, RelCT isa (R (4 * q)) (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) (R (4 * q + 4))) :
    ∀ n e, e + n = L.k * L.k → (e % 4 = 0 ∨ 4 * (L.k * L.k / 4) ≤ e) → RelCT isa (R e) (L.ents c e n) (R (e + n))
  | 0, e, _, _ => by simp only [Kem.ents]; exact nil_tr
  | 1, e, he, hq => by simp only [Kem.ents]; exact h1 e (by omega) (by omega)
  | 2, e, he, hq => by
    simp only [Kem.ents]
    exact RelCT.seq (h1 e (by omega) (by omega)) (ents_tr L c h1 h4 1 (e + 1) (by omega) (by omega))
  | 3, e, he, hq => by
    simp only [Kem.ents]
    have := ents_tr L c h1 h4 2 (e + 1) (by omega) (by omega)
    rw [show e + 1 + 2 = e + 3 by omega] at this
    exact RelCT.seq (h1 e (by omega) (by omega)) this
  | 4, e, he, hq => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega)
    rwa [show 4 * (e / 4) = e by omega] at this
  | n + 5, e, he, hq => by
    simp only [Kem.ents]
    have := h4 (e / 4) (by omega)
    rw [show 4 * (e / 4) = e by omega] at this
    have h' := ents_tr L c h1 h4 (n + 1) (e + 4) (by omega) (by omega)
    rw [show e + 4 + (n + 1) = e + (n + 5) by omega] at h'
    exact RelCT.seq this h'

theorem samples_tr' (L : Kem) (c : Callee4) {R : Nat → State → State → Prop}
    (h1 : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e →
      RelCT isa (R e) (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) (R (e + 1)))
    (h4 : ∀ q < L.k * L.k / 4, RelCT isa (R (4 * q)) (quad c L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) (R (4 * q + 4))) :
    RelCT isa (R 0) (L.samples c) (R (L.k * L.k)) := by
  have := ents_tr L c h1 h4 (L.k * L.k) 0 (by omega) (by omega)
  rwa [Nat.zero_add] at this

namespace KeyGen

open VG.Impl.MlKem.X86_64.KeyGen

/-! ## `G(d ‖ k)` -/

theorem sha3Suffix6 : BitVec.ofNat 8 6 = Spec.Sha3.sha3Suffix := by decide

/-- After `G`: `ρ` and `σ` at `G`, and `ρ` at `SB`. -/
structure KA (L : Kem) (σ s : State) : Prop where
  kc : KC σ s
  rho : bytesAt s.mem (pa s (sc oG)) 32 = KPke.kgRho L.p (kgD σ)
  sig : bytesAt s.mem (pa s sigP) 32 = KPke.kgSigma L.p (kgD σ)
  sb : bytesAt s.mem (pa s (sc oSB)) 32 = KPke.kgRho L.p (kgD σ)

theorem gRho_ok {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State} (h : KC σ s)
    (h15 : s.gpr .r15 = 1) : WP isa (gRho L) s fun s' => KA L σ s' ∧ s'.gpr .r15 = 1 := by
  have L₀ := h.lay W hp
  unfold gRho
  refine WP.seq (WP.mono (setB_okL L₀ (by decide) (by have := W.k; omega) (p := sc oNB) (v := L.k) W.nb)
    fun s₁ ⟨hP₁, hb₁⟩ => ?_)
  have h₁ := h.step W hp hP₁.b W.nbK
  have L₁ := h₁.lay W hp
  refine WP.seq (WP.mono (hash_ok (kgB_bases L) (ps := [((.rbp, 0), 32), (sc oNB, 1)]) (rate := 72) (out := sc oG)
    (len := 64) W.gH (show 6 < 256 by decide) L₁) fun s₂ ⟨hP₂, ho₂⟩ => ?_)
  have h₂ := h₁.step W hp hP₂.b W.gK
  have L₂ := h₂.lay W hp
  refine WP.mono (copy_okL L₂ (dst := sc oSB) (src := sc oG) (n := 32) (by decide) W.gC)
    fun s₃ ⟨hP₃, hb₃⟩ => ?_
  have h₃ := h₂.step W hp hP₃.b W.gCK
  -- The output of `G`.
  have hpc : pieces s₁ [((.rbp, 0), 32), (sc oNB, 1)] = kgD σ ++ [BitVec.ofNat 8 L.k] := by
    simp only [pieces, List.flatMap_cons, List.flatMap_nil, List.append_nil, h₁.d]
    rw [show pa s₁ (sc oNB) = pa s (sc oNB) from hP₁.pa rbx_cs, hb₁]
  rw [hpc, sha3Suffix6, ← sha3_512_eq] at ho₂
  have eG : pa s₂ (sc oG) = pa s₁ (sc oG) := hP₂.pa rbx_cs
  have hG : bytesAt s₂.mem (pa s₂ (sc oG)) 64 = Spec.Sha3.sha3_512 (kgD σ ++ [BitVec.ofNat 8 L.k]) := by
    rw [eG]; exact ho₂
  have hρ : bytesAt s₂.mem (pa s₂ (sc oG)) 32 = KPke.kgRho L.p (kgD σ) := by
    rw [← bytesAt_take _ _ (show 32 ≤ 64 by decide), hG]; rfl
  have hσ : bytesAt s₂.mem (pa s₂ sigP) 32 = KPke.kgSigma L.p (kgD σ) := by
    have e := bytesAt_drop s₂.mem (pa s₂ (sc oG)) (k := 32) (len := 64) (by decide)
    have e' : (bytesAt s₂.mem (pa s₂ (sc oG)) 64).drop 32 = bytesAt s₂.mem (pa s₂ sigP) 32 := by
      rw [e, pa, pa, off_add]
    rw [← e', hG]; rfl
  refine ⟨⟨h₃, ?_, ?_, ?_⟩, ?_⟩
  · rw [L₂.keepBytes hP₃.b W.gG]; exact hρ
  · rw [L₂.keepBytes hP₃.b W.gS]; exact hσ
  · rw [show pa s₃ (sc oSB) = pa s₂ (sc oSB) from hP₃.pa rbx_cs, hb₃, hρ]
  · rw [hP₃.cs .r15 (by decide), hP₂.cs .r15 (by decide), hP₁.cs .r15 (by decide), h15]

/-! ## The matrix -/

/-- After the first `e` entries of `Â`. -/
structure KB (L : Kem) (e : Nat) (σ s : State) : Prop where
  a : KA L σ s
  m : MatB L (KPke.kgRho L.p (kgD σ)) e s

theorem KB.zero {L : Kem} {σ s : State} (h : KA L σ s) (h15 : s.gpr .r15 = 1) : KB L 0 σ s :=
  ⟨h, MatB.zero L _ h15⟩

/-- The pieces of the key's state that a piece writing `ws` keeps. -/
theorem KA.keep {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s s' : State} (h : KA L σ s)
    {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hkc : kcChk L ws = true) (kG : keepB (kgB L) ws (sc oG) 32 = true)
    (kS : keepB (kgB L) ws sigP 32 = true) (kB : keepB (kgB L) ws (sc oSB) 32 = true) : KA L σ s' := by
  have L₀ := h.kc.lay W hp
  exact ⟨h.kc.step W hp hP hkc, by rw [L₀.keepBytes hP kG]; exact h.rho, by rw [L₀.keepBytes hP kS]; exact h.sig,
    by rw [L₀.keepBytes hP kB]; exact h.sb⟩

theorem sample_step {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {e : Nat} (he : e < L.k * L.k)
    (he' : 4 * (L.k * L.k / 4) ≤ e) {s : State} (h : KB L e σ s) :
    WP isa (sampleIJ (pS (L.pA + e)) (e / L.k) (e % L.k)) s (KB L (e + 1) σ) := by
  have hc := W.kb e he he'
  simp only [kbChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hij, hkc⟩, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (sampleIJ_ok L₀ (kgB_bases L) rbx_na (by have := div_lt_k he; omega) (by have := mod_lt_k he; omega) hij)
    fun s' ⟨hP, h15, hres⟩ => ⟨h.a.keep W hp hP hkc kG kS kB, h.m.single h.a.sb L₀ hP kA h15 hres⟩

theorem quad_step (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {q : Nat}
    (hq : q < L.k * L.k / 4) {s : State} (h : KB L (4 * q) σ s) :
    WP isa (quad v.callee L.k (4 * q) (pS (L.pA + 4 * q)) (pS L.pW)) s (KB L (4 * q + 4) σ) := by
  have hc := W.kq q hq
  simp only [kqChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hq', hkc⟩, kG⟩, kS⟩, kB⟩, kA⟩ := hc
  have hk := W.k
  have L₀ := h.a.kc.lay W hp
  refine WP.mono (quad_ok v L₀ (kgB_bases L) (by have : L.k * L.k ≤ 16 := Nat.mul_le_mul hk.2 hk.2; omega) hq')
    fun s' ⟨hP, h15, hres⟩ => ⟨h.a.keep W hp hP hkc kG kS kB, h.m.four h.a.sb L₀ hP kA h15 hres⟩

theorem samples_ok (v : Sample4Impl) {L : Kem} (W : KgWf L) {σ : State} (hp : (keyGenK L).pre σ) {s : State}
    (h : KB L 0 σ s) : WP isa (L.samples v.callee) s (KB L (L.k * L.k) σ) :=
  samples_ok' L v.callee (I := fun e => KB L e σ) (fun _ he he' _ hs => sample_step W hp he he' hs)
    (fun _ hq _ hs => quad_step v W hp hq hs) h

end KeyGen

end VG.Proof.MlKem.X86_64
