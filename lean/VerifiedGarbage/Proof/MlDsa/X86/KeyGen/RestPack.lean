import VerifiedGarbage.Proof.MlDsa.X86.KeyGen.RestBase

/-!
# ML-DSA key generation on x86 (32-bit): `s₁ ‖ s₂` packed, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`: its coefficients
are in `[-η, η]`), and `ŝ₁[j] = NTT(s₁[j])` (`nttS_piece`).
-/

namespace VG.Proof.MlDsa.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem.X86 VG.Proof.MlKem.X86.Top
open VG.Impl.MlDsa.X86.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack simpleBitPack)
open VG.Spec.Sha3 (bytesAt)

theorem coeff_val {m : Mem} {q : Addr} {f : Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega

theorem eta_le {p : Params} (hF : PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem eta_params {p : Params} (hF : PFacts p) : (p.η, p.η) ∈ Spec.MlDsa.bitPackParams := by
  rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> decide

theorem lenS_eq (p : Params) : lenS p = 32 * Spec.MlDsa.bitlen (p.η + p.η) := by
  rw [lenS, Nat.two_mul]

/-- The coefficients of a small polynomial are in `[-η, η]`, as `BitPack` needs. -/
theorem packIn {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x)) (hs : Small η x) :
    ∀ i < Spec.MlDsa.n, -(η : Int) ≤ Spec.MlDsa.modPm (coeffAt m q i).toNat Spec.MlDsa.q ∧
      Spec.MlDsa.modPm (coeffAt m q i).toNat Spec.MlDsa.q ≤ η := fun i hi => by
  have hx := small_mem hs hi
  rw [coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {A : Nat → Poly} {S : Nat → IPoly} {np nr : Nat} {s₀ s : State}
    (h : KR p A S np 0 nr s₀ s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem (Buf.addr s₀ (sB p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega); rwa [show p.ℓ + (r - p.ℓ) = r by omega] at this

section
variable {P : Prims} (hP : PrimsOk P) {p : Params} (hF : PFacts p)
include hP hF

theorem packS_piece {r : Nat} (hr : r < p.ℓ + p.k) : KP p (KRx p r 0 0) (KRx p (r + 1) 0 0) (packS P p r) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold packS
  refine Piece.mono (A := fun s₀ s => ∃ A S, KR p A S r 0 0 s₀ s ∧ PolyIs s.mem (Buf.addr s₀ (sB p r)) (toRq (S r)))
    ?_ (fun s₀ s _ ⟨A, S, h⟩ => ⟨A, S, h, h.sPoly hr⟩) fun _ _ _ h => h
  refine bp_piece (Y := YK p) hP.bitPack kS (oP (p.k * p.ℓ + r)) p.η p.η 2 (128 + lenS p * r) (lenS p)
    (eta_params hF) (lenS_eq p) (by layp hF) (Nat.le_of_eq (YK_stk p).symm) (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h, hs⟩ => ⟨h.ctx, hs.1, packIn (eta_le hF) hs (h.small r hr)⟩)
    fun s₀ s s' hp ⟨A, S, h, hs⟩ h' fr out => ⟨A, S, ?_⟩
  have hpos : 0 < lenS p := by rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hle : 128 + lenS p * r + lenS p ≤ oT0 p := by
    simp only [oT0]; rw [Nat.add_assoc, ← Nat.mul_succ]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _
  have hsf : SafeR p r 0 [⟨2, 128 + lenS p * r, lenS p⟩] := SafeR.sk hF (Nat.le_of_lt hr) (Nat.zero_le _) hpos
    (by omega) (.inr (Nat.le_refl _)) (.inl hle) (by rw [hF.sk]; omega)
  have k := h.keep hp (N := 80) (by omega) hsf (fun _ _ => by layp hF) fr h'
  refine { k with packs := fun r' hr' => ?_ }
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · exact k.packs r' hr'
  · rw [out, hs.2, Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

theorem nttS_piece {j : Nat} (hj : j < p.ℓ) :
    KP p (KRx p (p.ℓ + p.k) j 0) (KRx p (p.ℓ + p.k) (j + 1) 0) (nttS P p j) := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  unfold nttS
  refine Piece.mono (A := fun s₀ s => ∃ A S, KR p A S (p.ℓ + p.k) j 0 s₀ s)
    ?_ (fun _ _ _ h => h) fun _ _ _ h => h
  refine inPlace_piece (Y := YK p) hP.ntt kS (oP (p.k * p.ℓ + j)) kS oSS (by layp hF) (Nat.le_of_eq (YK_stk p).symm)
    (ht := .block []) (by kernel_rfl)
    (fun s₀ s _ ⟨A, S, h⟩ => ⟨h.ctx, (h.s1 j hj).1⟩)
    fun s₀ s s' hp ⟨A, S, h⟩ h' fr out => ⟨A, S, ?_⟩
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  have hs : SafeR p (p.ℓ + p.k) 0 [sB p j, ssB 1024] :=
    (SafeR.sc hF (Nat.le_refl _) (Nat.zero_le _) (by decide) (.inr (by simp only [oACC, oP]; omega))
      (.inr (.inl (by simp only [oP]; omega))) (by simp only [scrLen, hF.sw, oP]; omega)).append (bs₁ := [_])
    (SafeR.sc (o := oSS) (l := 1024) hF (Nat.le_refl _) (Nat.zero_le _) (by decide) (.inr (by decide))
      (.inl (by decide)) (by simp only [scrLen, hF.sw, oSS]; omega))
  exact { ctx := h'
          good := by rw [acc_keep hp (N := 80) (by omega) hs.acc fr]; exact h.good
          small := h.small
          aS := fun e he => keepPolyD hp (stkN (by omega)) (hs.aS e he) fr (h.aS e he)
          s2 := fun i hi => keepPolyD hp (stkN (by omega)) (hs.s2 i hi) fr (h.s2 i hi)
          s1 := fun j' hj' => if e : j' = j then by
              subst e; rw [ifp (Nat.lt_succ_self j'), ← hS.2]; exact out
            else by
              have := keepPolyD hp (stkN (by omega)) (by layp hF) fr (h.s1 j' hj')
              by_cases hlt : j' < j
              · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega) (ntt (toRq (S j'))) (toRq (S j'))] at this
              · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega) (ntt (toRq (S j'))) (toRq (S j'))] at this
          pk0 := by rw [keepBytes hp (stkN (by omega)) hs.pk0 fr]; exact h.pk0
          sk0 := by rw [keepBytes hp (stkN (by omega)) hs.sk0 fr]; exact h.sk0
          sk1 := by rw [keepBytes hp (stkN (by omega)) hs.sk1 fr]; exact h.sk1
          packs := fun r hr => by rw [keepBytes hp (stkN (by omega)) (hs.packs r hr) fr]; exact h.packs r hr
          rows := fun _ h => absurd h (Nat.not_lt_zero _) }

end

end VG.Proof.MlDsa.X86.KeyGen
