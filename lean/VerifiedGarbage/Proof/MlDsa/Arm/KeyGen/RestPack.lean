import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestBase

/-!
# ML-DSA key generation on 32-bit ARM: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] =
NTT(s₁[j])` in place (`nttS_piece`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack modPm q n)
open VG.Proof.MlDsa.KeyGen (Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {a : Addr} {f : Poly} (h : PolyIs m a f) {i : Nat} (hi : i < 256) :
    (coeffAt m a i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem small_coeff {m : Mem} {a : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m a (toRq x))
    (hs : Small η x) : ∀ i < n, -(η : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ η :=
  fun i hi => by
    have hx := small_mem hs hi
    rw [coeff_val h hi]
    simp only [toRq, Vector.getElem_map]
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
    exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega

theorem eta_le {p : Params} (hF : PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem eta_params {p : Params} (hF : PFacts p) : (p.η, p.η) ∈ Spec.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nr : Nat} {s : State} (h : KR p STK σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega); rwa [show p.ℓ + (r - p.ℓ) = r by omega] at this

/-- The states after the copies, and the first `np` entries packed, `nj` in
the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (STK : Nat) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, KR p STK σ A S R np nj nr s

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-! ## `BitPack` of `s₁ ‖ s₂` -/

omit hP hS in
theorem packS_m {σ : State} {r : Nat} (hr : r < p.ℓ + p.k) :
    BpOk (lay p STK σ) kWb (sP p r) p.η p.η (.r6, 128 + lenS p * r) (lenS p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.sk, hlen]⟩, show ix Reg.r6 ∈ kWb by decide,
    by lsep hF [hF.sk, hlen], eta_params hF, lenS_eq p⟩

theorem packS_ok {r : Nat} (hr : r < p.ℓ + p.k) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : KR p STK σ A S' R r 0 0 s) : WP isa (packS P p r) s (KR p STK σ A S' R (r + 1) 0 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSp := h.sPoly hr
  unfold packS bitPackAt
  refine bp_ok hP.bitPack hs (by omega) (packS_m hF hr) hSp.1 (small_coeff (eta_le hF) hSp (h.small r hr))
    fun s' k' hb => ?_
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hk' := h.keep hF k' ((KRChk.c4 (o := 128 + lenS p * r) (n := lenS p) hF (Nat.le_of_lt hr) (Nat.zero_le _)
    (by omega) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega)).append (W₁ := [_])
    (KRChk.stk hF (Nat.le_of_lt hr) (Nat.zero_le _)))
  refine ⟨hk'.kc, hk'.r11, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · show bytesAt s'.mem (lpa (lay p STK σ) (.r6, 128 + lenS p * r')) (lenS p) = _
    rw [hb]
    show bitPack ((polyAt s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r')))).map _) _ _ = _
    rw [hSp.2, Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

theorem packS_two {r : Nat} (hr : r < p.ℓ + p.k) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧
      PolyIs x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (polyAt x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) ∧
      PolyIs y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (polyAt y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r)))) ∧
      (∃ x' : IPoly, PolyIs x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq x') ∧ Small p.η x') ∧
      (∃ y' : IPoly, PolyIs y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + r))) (toRq y') ∧ Small p.η y'))
      (packS P p r) fun _ _ => True := by
  unfold packS bitPackAt
  exact bp_tr hP.bitPack (by omega) (packS_m hF hr) fun x y ⟨T, rx, ry, ⟨x', hx, sx⟩, ⟨y', hy, sy⟩⟩ =>
    ⟨T.1, T.2.1, T.2.2, rx.1, ry.1, small_coeff (eta_le hF) hx sx, small_coeff (eta_le hF) hy sy⟩

theorem packS_piece {r : Nat} (hr : r < p.ℓ + p.k) :
    KPiece p STK (KRx p STK r 0 0) (KRx p STK (r + 1) 0 0) (packS P p r) :=
  ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (packS_ok hP hF hS hr h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (RelCT.exists_ fun σ => packS_two hP hF hS hr σ) fun σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨(h₁.sPoly hr).1, rfl⟩, by rw [lay_pub pub]; exact ⟨(h₂.sPoly hr).1, rfl⟩,
        ⟨_, h₁.sPoly hr, h₁.small r hr⟩, by rw [lay_pub pub]; exact ⟨_, h₂.sPoly hr, h₂.small r hr⟩⟩⟩

/-! ## `NTT` of `s₁` -/

omit hP hS in
theorem nttS_m {σ : State} {j : Nat} (hj : j < p.ℓ) : PtrIn (lay p STK σ) (sP p j) 1024 ∧ PtrIn (lay p STK σ) (sc oSS) 1024 ∧
    sepB (lay p STK σ).sizes (tri (sP p j) 1024) (tri (sc oSS) 1024) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, by lsep hF⟩

theorem nttS_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : KR p STK σ A S' R (p.ℓ + p.k) j 0 s) :
    WP isa (nttS P p j) s (KR p STK σ A S' R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hs := h.kc.site
  have hSj := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hSj
  obtain ⟨m1, m2, m3⟩ := nttS_m hF (STK := STK) (σ := σ) hj
  unfold nttS nttAt
  refine ip_ok (t := ntt) hP.ntt hs (by omega) m1 m2 (show ix Reg.r7 ∈ kWb by decide)
    (show ix Reg.r7 ∈ kWb by decide) m3 hSj.1 fun s' k' hb => ?_
  have hL := hs.ok
  have hle : lenS p ≤ 2 ^ 64 := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hpk : ∀ r < p.ℓ + p.k, sepAll [scrLen p, STK, 32, p.pkLen, p.skLen] (4, 128 + lenS p * r, lenS p)
      [tri (sP p j) 1024, tri (sc oSS) 1024, (1, 0, STK)] = true := fun r hr => by
    rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.sk, hlen]
  refine ⟨h.kc.keep k' (by lsep hF [kcChk]), (k'.cs .r11 (by decide) (by decide)).trans h.r11, h.good, h.small,
    fun e he => polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.aS e he),
    fun i hi => polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.s2 i hi), fun j' hj' => ?_,
    by rw [bytes_keepW hL k'.frame (i := 3) (o := 0) (l := 32) (by lsep hF [hF.pk]) (by decide) (by decide)]
       exact h.pk0,
    by rw [bytes_keepW hL k'.frame (i := 4) (o := 0) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
       exact h.sk0,
    by rw [bytes_keepW hL k'.frame (i := 4) (o := 32) (l := 32) (by lsep hF [hF.sk]) (by decide) (by decide)]
       exact h.sk1,
    fun r hr => by rw [bytes_keepW hL k'.frame (hpk r hr) (by decide) hle]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩
  by_cases e : j' = j
  · subst e
    rw [ifp (Nat.lt_succ_self _)]
    show PolyIs s'.mem (lpa (lay p STK σ) (sP p j')) _
    rw [← hSj.2]; exact hb
  · have := polyIs_keepW hL k'.frame (by lsep hF) (by decide) rfl (h.s1 j' hj')
    by_cases hlt : j' < j
    · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega) (ntt (toRq (S' j'))) (toRq (S' j'))] at this
    · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega) (ntt (toRq (S' j'))) (toRq (S' j'))] at this

theorem nttS_two {j : Nat} (hj : j < p.ℓ) (σ : State) :
    RelCT isa (fun x y => Two (lay p STK σ) kWb STK x y ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j))) ∧
      Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))) (nttS P p j) fun _ _ => True := by
  obtain ⟨m1, m2, m3⟩ := nttS_m hF (STK := STK) (σ := σ) hj
  unfold nttS nttAt
  exact ip_tr (t := ntt) hP.ntt (by omega) m1 m2 (show ix Reg.r7 ∈ kWb by decide) (show ix Reg.r7 ∈ kWb by decide)
    m3 fun x y ⟨T, rx, ry⟩ => ⟨T.1, T.2.1, T.2.2, rx, ry⟩

theorem nttS_piece {j : Nat} (hj : j < p.ℓ) :
    KPiece p STK (KRx p STK (p.ℓ + p.k) j 0) (KRx p STK (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (nttS_ok hP hF hS hj h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (RelCT.exists_ fun σ => nttS_two hP hF hS hj σ) fun σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, (h₁.s1 j hj).1, by rw [lay_pub pub]; exact (h₂.s1 j hj).1⟩⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
