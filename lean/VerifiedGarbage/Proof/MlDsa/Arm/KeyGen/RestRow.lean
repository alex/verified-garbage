import VerifiedGarbage.Proof.MlDsa.Arm.KeyGen.RestPack

/-!
# ML-DSA key generation on 32-bit ARM: the rows of `t`

Untrusted: everything here is checked by Lean. Row `i` of `t`: the sum of
the products `Â[i, j] ŝ₁[j]` in `t` (`rowMul_ok`, `rowMulAdd_ok`), `NTT⁻¹` of
it plus `s₂[i]` (`rowInv_ok`, `rowAdd_ok`), then `Power2Round` (`rowP2r_ok`)
and `t₁[i]` packed to `pk` and `t₀[i]` to `sk` (`rowSbp_ok`, `rowBp_ok`).
-/

namespace VG.Proof.MlDsa.Arm.KeyGen

open VG VG.Arm VG.Proof.MlKem.Arm
open VG.Impl.MlDsa.Arm.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt nttInv add multiplyNTT polyAt natPolyAt coeffAt Reduced PolyIs
  NatPolyIs bitPack simpleBitPack power2Round ofInt modPm q n)
open VG.Proof.MlDsa.KeyGen (dotK tK t1K t0K ifp ifn idx_lt)
open VG.Spec.Sha3 (bytesAt)

/-- The polynomial `t`, `t₁` and `t₀` of the layout. -/
abbrev oT (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k)
abbrev oT1 (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k + 1)
abbrev oT0' (p : Params) : Nat := oP (p.k * p.ℓ + p.ℓ + p.k + 2)

/-- The `t` so far. -/
abbrev tIs (p : Params) (STK : Nat) (g : (Nat → Poly) → (Nat → IPoly) → Poly) (σ : State) (A : Nat → Poly)
    (S : Nat → IPoly) (s : State) : Prop := PolyIs s.mem ((lay p STK σ).A 0 (oT p)) (g A S)

/-- In row `i`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (STK : Nat) (i : Nat)
    (f : State → (Nat → Poly) → (Nat → IPoly) → State → Prop) (σ s : State) : Prop :=
  ∃ A S R, KR p STK σ A S R (p.ℓ + p.k) p.ℓ i s ∧ f σ A S s

theorem KR.polyA {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nj nr : Nat} {s : State} (h : KR p STK σ A S R np nj nr s) {i j : Nat} (hi : i < p.k) (hj : j < p.ℓ) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.ℓ * i + j))) (A (p.ℓ * i + j)) := h.aS _ (idx_lt hi hj)

theorem KR.polyS {p : Params} {STK : Nat} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 32}
    {np nr : Nat} {s : State} (h : KR p STK σ A S R np p.ℓ nr s) {j : Nat} (hj : j < p.ℓ) :
    PolyIs s.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j))) (ntt (toRq (S j))) := by
  have := h.s1 j hj; rwa [ifp hj] at this

theorem modPm_t0 (t : Poly) :
    ((t.map fun c => ofInt (power2Round c).2).map fun c => modPm c.val q) = t.map fun c => (power2Round c).2 := by
  rw [Vector.map_map]
  refine Vector.map_congr_left fun c _ => ?_
  have := Proof.MlDsa.KeyGen.power2Round_snd c
  exact Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)

theorem t0_coeff {m : Mem} {a : Addr} {t : Poly} (h : PolyIs m a (t.map fun c => ofInt (power2Round c).2)) :
    ∀ i < n, -((4095 : Nat) : Int) ≤ modPm (coeffAt m a i).toNat q ∧ modPm (coeffAt m a i).toNat q ≤ ((4096 : Nat) : Int) :=
  fun j hj => by
    rw [coeff_val h hj]
    simp only [Vector.getElem_map]
    have := Proof.MlDsa.KeyGen.power2Round_snd (t[j]'hj)
    rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
    omega

theorem t1_bound {m : Mem} {a : Addr} {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {i : Nat}
    (h1 : NatPolyIs m a (t1K p A S i)) : ∀ j < n, (coeffAt m a j).toNat ≤ 1023 := fun j hj => by
  rw [show (coeffAt m a j).toNat = (t1K p A S i)[j]'hj from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [t1K, Vector.getElem_map]
  have := Proof.MlDsa.KeyGen.power2Round_fst ((tK p A S i)[j]'hj)
  omega

section
variable {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
  {i : Nat} (hi : i < p.k)
include hP hF hS hi

/-! ## The calls, one by one -/

/-- `t = Â[i, 0] ŝ₁[0]`. -/
theorem rowMul_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) :
    WP isa (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => dotK p A S i 1) σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega)
  have hA := h.polyA hi (j := 0) (by omega)
  rw [Nat.add_zero] at hx0 hA
  have hS0 := h.polyS (j := 0) (by omega)
  rw [Nat.add_zero] at hS0
  refine mul_ok hP.mul h.kc.site (by omega) (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
      by lsep hF, by lsep hF⟩ hA.1 hS0.1 fun s' k' hb => ⟨h.keep hF k' (by krchk hF), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_one, ← hA.2, ← hS0.2]
  exact hb

/-- `t = t + Â[i, j] ŝ₁[j]`. -/
theorem rowMulAdd_ok {j : Nat} (hj : j < p.ℓ) {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32}
    {s : State} (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => dotK p A S i j) σ A S' s) :
    WP isa (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => dotK p A S i (j + 1)) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  have hA := h.polyA hi hj
  have hSj := h.polyS hj
  refine mulAdd_ok hP.mulAdd h.kc.site (by omega) (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
      by lsep hF, by lsep hF⟩ ht.1 hA.1 hSj.1 fun s' k' hb => ⟨h.keep hF k' (by krchk hF), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.dotK_succ, ← hA.2, ← hSj.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem tP_m {σ : State} : PtrIn (lay p STK σ) (tP p) 1024 ∧ PtrIn (lay p STK σ) (sc oSS) 1024 ∧
    sepB (lay p STK σ).sizes (tri (tP p) 1024) (tri (sc oSS) 1024) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, by lsep hF⟩

/-- `t = NTT⁻¹(t)`. -/
theorem rowInv_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => dotK p A S i p.ℓ) σ A S' s) :
    WP isa (invNttAt P (tP p)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => nttInv (dotK p A S i p.ℓ)) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  obtain ⟨m1, m2, m3⟩ := tP_m hF (σ := σ)
  unfold invNttAt
  refine ip_ok (t := nttInv) hP.invNtt h.kc.site (by omega) m1 m2 (show ix Reg.r7 ∈ kWb by decide)
    (show ix Reg.r7 ∈ kWb by decide) m3 ht.1 fun s' k' hb => ⟨h.keep hF k' (by krchk hF), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [← ht.2]
  exact hb

/-- `t = t + s₂[i]`. -/
theorem rowAdd_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s)
    (ht : tIs p STK (fun A S => nttInv (dotK p A S i p.ℓ)) σ A S' s) :
    WP isa (addAt P (tP p) (sP p (p.ℓ + i))) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ tIs p STK (fun A S => tK p A S i) σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hS2 := h.s2 i hi
  refine add_ok hP.add h.kc.site (by omega) (f := tP p) (g := sP p (p.ℓ + i))
    ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide, by lsep hF⟩ ht.1 hS2.1
    fun s' k' hb => ⟨h.keep hF k' (by krchk hF), ?_⟩
  show PolyIs s'.mem (lpa (lay p STK σ) (tP p)) _
  dsimp only
  rw [Proof.MlDsa.KeyGen.tK, ← hS2.2, ← ht.2]
  exact hb

omit hP hS hi in
theorem p2r_m {σ : State} : P2rOk (lay p STK σ) kWb (tP p) (t1P p) (t0P p) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
    show ix Reg.r7 ∈ kWb by decide, by lsep hF, by lsep hF, by lsep hF⟩

/-- After `Power2Round`. -/
abbrev p2rIs (p : Params) (STK i : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  NatPolyIs s.mem ((lay p STK σ).A 0 (oT1 p)) (t1K p A S i) ∧
    PolyIs s.mem ((lay p STK σ).A 0 (oT0' p)) ((tK p A S i).map fun c => ofInt (power2Round c).2)

/-- `Power2Round` of `t`. -/
theorem rowP2r_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (ht : tIs p STK (fun A S => tK p A S i) σ A S' s) :
    WP isa (power2RoundAt P (tP p) (t1P p) (t0P p)) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ p2rIs p STK i σ A S' s' := by
  dsimp only [tIs] at ht
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine p2r_ok hP.power2Round h.kc.site (by omega) (p2r_m hF) ht.1 fun s' k' h1 h0 =>
    ⟨h.keep hF k' (by krchk hF), ?_, ?_⟩
  · show NatPolyIs s'.mem (lpa (lay p STK σ) (t1P p)) _
    rw [t1K, ← ht.2]; exact h1
  · show PolyIs s'.mem (lpa (lay p STK σ) (t0P p)) _
    rw [← ht.2]; exact h0

/-- After `t₁[i]` to `pk`. -/
abbrev sbpIs (p : Params) (STK i : Nat) (σ : State) (A : Nat → Poly) (S : Nat → IPoly) (s : State) : Prop :=
  PolyIs s.mem ((lay p STK σ).A 0 (oT0' p)) ((tK p A S i).map fun c => ofInt (power2Round c).2) ∧
    bytesAt s.mem ((lay p STK σ).A 3 (32 + 320 * i)) 320 = simpleBitPack (t1K p A S i) 1023

omit hP hS in
theorem sbp_m {σ : State} : SbpOk (lay p STK σ) kWb (t1P p) 1023 (.r5, 32 + 320 * i) 320 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.pk]⟩, show ix Reg.r5 ∈ kWb by decide, by lsep hF [hF.pk],
    by decide, by decide⟩

/-- `t₁[i]` to `pk`. -/
theorem rowSbp_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h1 : p2rIs p STK i σ A S' s) :
    WP isa (simpleBitPackAt P (t1P p) 1023 (.r5, 32 + 320 * i) 320) s fun s' =>
      KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s' ∧ sbpIs p STK i σ A S' s' := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine sbp_ok hP.simpleBitPack h.kc.site (by omega) (sbp_m hF hi) (t1_bound h1.1) fun s' k' hb =>
    ⟨h.keep hF k' (by krchk hF), polyIs_keepW h.kc.site.ok k'.frame (by lsep hF [hF.pk]) (by decide) rfl h1.2, ?_⟩
  show bytesAt s'.mem (lpa (lay p STK σ) (.r5, 32 + 320 * i)) 320 = _
  rw [hb]
  exact congrArg (simpleBitPack · 1023) h1.1

omit hP hS in
theorem bp_m {σ : State} : BpOk (lay p STK σ) kWb (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416 := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨⟨sc_ok _, by lsep hF⟩, ⟨rfl, by lsep hF [hF.sk, hlen]⟩, show ix Reg.r6 ∈ kWb by decide,
    by lsep hF [hF.sk, hlen], by decide, by decide⟩

/-- `t₀[i]` to `sk`. -/
theorem rowBp_ok {σ : State} {A : Nat → Poly} {S' : Nat → IPoly} {R : BitVec 32} {s : State}
    (h : KR p STK σ A S' R (p.ℓ + p.k) p.ℓ i s) (h0 : sbpIs p STK i σ A S' s) :
    WP isa (bitPackAt P (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416) s
      (KR p STK σ A S' R (p.ℓ + p.k) p.ℓ (i + 1)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  unfold bitPackAt
  refine bp_ok hP.bitPack h.kc.site (by omega) (bp_m hF hi) h0.1.1 (t0_coeff h0.1) fun s' k' hb => ?_
  have hk' := h.keep hF k' (by krchk hF)
  refine ⟨hk'.kc, hk'.r11, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1, hk'.packs,
    fun i' hi' => ?_⟩
  rcases (by omega : i' < i ∨ i' = i) with hi' | rfl
  · exact hk'.rows i' hi'
  · refine ⟨?_, ?_⟩
    · rw [bytes_keepW h.kc.site.ok k'.frame (i := 3) (o := 32 + 320 * i') (l := 320)
        (by rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;> lsep hF [hF.pk, hF.sk, hlen]) (by decide) (by decide)]
      exact h0.2
    · show bytesAt s'.mem (lpa (lay p STK σ) (.r6, oT0 p + 416 * i')) 416 = _
      rw [hb]
      show bitPack ((polyAt s.mem ((lay p STK σ).A 0 (oT0' p))).map _) _ _ = _
      rw [h0.1.2, modPm_t0]
      rfl

/-! ## The pieces of a row -/

theorem rowMul_piece :
    KPiece p STK (KRx p STK (p.ℓ + p.k) p.ℓ i) (RowI p STK i (tIs p STK fun A S => dotK p A S i 1))
      (mulAt P (tP p) (aP (p.ℓ * i)) (sP p 0)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt (j := 0) hi (by omega)
  rw [Nat.add_zero] at hx0
  refine ⟨fun _ _ _ ⟨A, S', R, h⟩ => WP.mono (rowMul_ok hP hF hS hi h) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ)))) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oP (p.ℓ * i))) ∧ Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ)))))
      (RelCT.exists_ fun σ => mul_tr hP.mul (by omega) (h := tP p) (f := aP (p.ℓ * i)) (g := sP p 0)
        ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
          by lsep hF, by lsep hF⟩ fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩
  have a₁ := h₁.polyA hi (j := 0) (by omega); have a₂ := h₂.polyA hi (j := 0) (by omega)
  have s₁ := h₁.polyS (j := 0) (by omega); have s₂ := h₂.polyS (j := 0) (by omega)
  rw [Nat.add_zero] at a₁ a₂ s₁ s₂
  rw [← lay_pub pub] at a₂ s₂
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨a₁.1, s₁.1⟩, ⟨a₂.1, s₂.1⟩⟩

theorem rowMulAdd_piece {j : Nat} (hj : j < p.ℓ) :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => dotK p A S i j))
      (RowI p STK i (tIs p STK fun A S => dotK p A S i (j + 1))) (mulAddAt P (tP p) (aP (p.ℓ * i + j)) (sP p j)) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  have hx0 := idx_lt hi hj
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowMulAdd_ok hP hF hS hi hj h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.ℓ * i + j))) ∧
        Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced y.mem ((lay p STK σ).A 0 (oP (p.ℓ * i + j))) ∧
        Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + j)))))
      (RelCT.exists_ fun σ => mulAdd_tr hP.mulAdd (by omega) (h := tP p) (f := aP (p.ℓ * i + j)) (g := sP p j)
        ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide,
          by lsep hF, by lsep hF⟩ fun x y ⟨T, ⟨a, b, c⟩, ⟨d, e, f⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d, e, f⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have a₂ := (h₂.polyA hi hj).1; have s₂ := (h₂.polyS hj).1; have t₂' := t₂.1
  rw [← lay_pub pub] at a₂ s₂ t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.polyA hi hj).1, (h₁.polyS hj).1⟩, ⟨t₂', a₂, s₂⟩⟩

theorem rowInv_piece :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => dotK p A S i p.ℓ))
      (RowI p STK i (tIs p STK fun A S => nttInv (dotK p A S i p.ℓ))) (invNttAt P (tP p)) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowInv_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧ Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧
      Reduced y.mem ((lay p STK σ).A 0 (oT p)))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := tP_m hF (σ := σ)
        unfold invNttAt
        exact ip_tr (t := nttInv) hP.invNtt (by omega) m1 m2 (show ix Reg.r7 ∈ kWb by decide)
          (show ix Reg.r7 ∈ kWb by decide) m3 fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t₁.1, t₂'⟩

theorem rowAdd_piece :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => nttInv (dotK p A S i p.ℓ)))
      (RowI p STK i (tIs p STK fun A S => tK p A S i)) (addAt P (tP p) (sP p (p.ℓ + i))) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowAdd_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced x.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i))))) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oT p)) ∧ Reduced y.mem ((lay p STK σ).A 0 (oP (p.k * p.ℓ + (p.ℓ + i))))))
      (RelCT.exists_ fun σ => add_tr hP.add (by omega) (f := tP p) (g := sP p (p.ℓ + i))
        ⟨⟨sc_ok _, by lsep hF⟩, ⟨sc_ok _, by lsep hF⟩, show ix Reg.r7 ∈ kWb by decide, by lsep hF⟩
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1; have s₂ := (h₂.s2 i hi).1
  rw [← lay_pub pub] at t₂' s₂
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1, (h₁.s2 i hi).1⟩, ⟨t₂', s₂⟩⟩

theorem rowP2r_piece :
    KPiece p STK (RowI p STK i (tIs p STK fun A S => tK p A S i)) (RowI p STK i (p2rIs p STK i))
      (power2RoundAt P (tP p) (t1P p) (t0P p)) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, ht⟩ => WP.mono (rowP2r_ok hP hF hS hi h ht) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧ Reduced x.mem ((lay p STK σ).A 0 (oT p)) ∧
      Reduced y.mem ((lay p STK σ).A 0 (oT p)))
      (RelCT.exists_ fun σ => p2r_tr hP.power2Round (by omega) (p2r_m hF)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t₁.1, t₂'⟩

theorem rowSbp_piece :
    KPiece p STK (RowI p STK i (p2rIs p STK i)) (RowI p STK i (sbpIs p STK i))
      (simpleBitPackAt P (t1P p) 1023 (.r5, 32 + 320 * i) 320) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, h1⟩ => WP.mono (rowSbp_ok hP hF hS hi h h1) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (∀ j < n, (coeffAt x.mem ((lay p STK σ).A 0 (oT1 p)) j).toNat ≤ 1023) ∧
      (∀ j < n, (coeffAt y.mem ((lay p STK σ).A 0 (oT1 p)) j).toNat ≤ 1023))
      (RelCT.exists_ fun σ => sbp_tr hP.simpleBitPack (by omega) (sbp_m hF hi)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have t₂' := t1_bound t₂.1
  rw [← lay_pub pub] at t₂'
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, t1_bound t₁.1, t₂'⟩

theorem rowBp_piece :
    KPiece p STK (RowI p STK i (sbpIs p STK i)) (KRx p STK (p.ℓ + p.k) p.ℓ (i + 1))
      (bitPackAt P (t0P p) 4095 4096 (.r6, oT0 p + 416 * i) 416) := by
  refine ⟨fun _ _ _ ⟨A, S', R, h, h0⟩ => WP.mono (rowBp_ok hP hF hS hi h h0) fun _ h => ⟨A, S', R, h⟩,
    rel_of (Q := fun x y => ∃ σ, Two (lay p STK σ) kWb STK x y ∧
      (Reduced x.mem ((lay p STK σ).A 0 (oT0' p)) ∧ ∀ j < n, -((4095 : Nat) : Int) ≤
        modPm (coeffAt x.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ∧
        modPm (coeffAt x.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ≤ ((4096 : Nat) : Int)) ∧
      (Reduced y.mem ((lay p STK σ).A 0 (oT0' p)) ∧ ∀ j < n, -((4095 : Nat) : Int) ≤
        modPm (coeffAt y.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ∧
        modPm (coeffAt y.mem ((lay p STK σ).A 0 (oT0' p)) j).toNat q ≤ ((4096 : Nat) : Int)))
      (RelCT.exists_ fun σ => by
        unfold bitPackAt
        exact bp_tr hP.bitPack (by omega) (bp_m hF hi)
          fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, c, b, d⟩) ?_⟩
  intro σ₁ _ _ _ _ _ pub ⟨_, _, _, h₁, t₁⟩ ⟨_, _, _, h₂, t₂⟩
  have r₂ := t₂.1.1; have c₂ := t0_coeff t₂.1
  rw [← lay_pub pub] at r₂ c₂
  exact ⟨σ₁, kc_twoL pub h₁.kc h₂.kc, ⟨t₁.1.1, t0_coeff t₁.1⟩, ⟨r₂, c₂⟩⟩

end

end VG.Proof.MlDsa.Arm.KeyGen
