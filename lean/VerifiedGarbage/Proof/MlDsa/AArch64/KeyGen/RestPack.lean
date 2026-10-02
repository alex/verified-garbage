import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.RestBase

/-!
# ML-DSA key generation on AArch64: `s₁ ‖ s₂` to `sk`, and `ŝ₁`

Each entry of `s₁ ‖ s₂`, `BitPack`ed to `sk` (`packS_piece`), then `ŝ₁[j] =
NTT(s₁[j])` in place (`nttS_piece`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt coeffAt Reduced PolyIs bitPack)
open VG.Proof.MlDsa.KeyGen (Small ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## The coefficients of a small polynomial -/

theorem coeff_val {m : Mem} {q : Addr} {f : Poly} (h : PolyIs m q f) {i : Nat} (hi : i < 256) :
    (coeffAt m q i).toNat = (f[i]'hi).val := by
  have e := congrArg (fun g : Poly => (g[i]'hi).val) h.2
  simp only [polyAt, Vector.getElem_ofFn, Fin.val_ofNat] at e
  rw [← e, Nat.mod_eq_of_lt (h.1 i hi)]

theorem small_mem {η : Nat} {x : IPoly} (h : Small η x) {i : Nat} (hi : i < 256) :
    -(η : Int) ≤ x[i] ∧ x[i] ≤ η := h _ (Vector.mem_toList_iff.mpr (Vector.getElem_mem hi))

theorem range_of {m : Mem} {q : Addr} {η : Nat} (hη : η ≤ 4) {x : IPoly} (h : PolyIs m q (toRq x))
    (hs : Small η x) : BpRange m q η η := by
  intro i hi
  have hx := small_mem hs hi
  rw [coeff_val h hi]
  simp only [toRq, Vector.getElem_map]
  rw [Proof.MlDsa.KeyGen.modPm_ofInt (by omega) (by omega)]
  exact hx

theorem small_big {η : Nat} (hη : η ≤ 4) {x : IPoly} (hs : Small η x) :
    ∀ c ∈ x.toList, -4190208 ≤ c ∧ c ≤ 4190208 := fun c hc => by
  have := hs c hc; omega

theorem eta_le {p : Params} (hF : PFacts p) : p.η ≤ 4 := by rcases hF.eta with ⟨h, _⟩ | ⟨h, _⟩ <;> omega

theorem bpOk_eta {p : Params} (hF : PFacts p) : BpOk p.η p.η (lenS p) := by
  rcases hF.eta with ⟨h, e⟩ | ⟨h, e⟩ <;> exact ⟨by rw [h]; decide, by rw [e, h]; decide, by rw [e, h]; decide⟩

/-- The entry `r` of `s₁ ‖ s₂`, before `NTT`. -/
theorem KR.sPoly {p : Params} {σ : State} {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {np nr : Nat}
    {s : State} (h : KR p σ A S R np 0 nr s) {r : Nat} (hr : r < p.ℓ + p.k) :
    PolyIs s.mem (pa s (sP p r)) (toRq (S r)) := by
  by_cases hl : r < p.ℓ
  · have := h.s1 r hl; rwa [ifn (Nat.not_lt_zero r)] at this
  · have := h.s2 (r - p.ℓ) (by omega); rwa [show p.ℓ + (r - p.ℓ) = r by omega] at this

/-! ## `BitPack` of `s₁ ‖ s₂` -/

theorem packS_chk {p : Params} (hF : PFacts p) {r : Nat} (hr : r < p.ℓ + p.k) :
    rwChk kgR (kgW p) (sP p r) 1024 (.x27, 128 + lenS p * r) (lenS p) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have hlr : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  unfold rwChk
  lay [hF.pk, hF.sk]

theorem packS_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S' σ) {r : Nat} (hr : r < p.ℓ + p.k) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R r 0 0 s) : WP isa (packS P p r) s (KR p σ A S R (r + 1) 0 0) := by
  have L := h.kc.lay hF hp
  have hS := h.sPoly hr
  unfold packS
  refine WP.mono (bpAt_ok hP.s64 hP.bitPack L (packS_chk hF hr) (bpOk_eta hF) hS.1
    (range_of (eta_le hF) hS (h.small r hr))) fun s' ⟨hP', x', hb⟩ => ?_
  have hk' := h.keep hF hp hP' x' (by
    have hkl := hF.kl; have hl := hF.l; have hk := hF.k
    have hlr : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    have hlr' : ∀ r' < r, lenS p * r' + lenS p ≤ lenS p * r := fun r' hr' => by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    krchk hF)
  refine ⟨hk'.kc, hk'.x24, hk'.good, hk'.small, hk'.aS, hk'.s2, hk'.s1, hk'.pk0, hk'.sk0, hk'.sk1,
    fun r' hr' => ?_, hk'.rows⟩
  rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
  · exact hk'.packs r' hr'
  · rw [hP'.pa (show Reg.x27 ∈ bases by decide), hb, hS.2,
      Proof.MlDsa.KeyGen.modPm_toRq (small_big (eta_le hF) (h.small r' hr))]

/-- The states after the copies, and the first `np` entries packed, `nj` in the NTT domain and `nr` rows. -/
abbrev KRx (p : Params) (np nj nr : Nat) (σ s : State) : Prop := ∃ A S R, KR p σ A S R np nj nr s

theorem packS_tr {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : RelCT isa (R p S' (KRx p r 0 0)) (packS P p r) fun _ _ => True := by
  refine rel_of (Q := fun x y => Two p S' x y ∧ (Reduced x.mem (pa x (sP p r)) ∧ BpRange x.mem (pa x (sP p r)) p.η p.η) ∧
    (Reduced y.mem (pa y (sP p r)) ∧ BpRange y.mem (pa y (sP p r)) p.η p.η)) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ =>
      ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, ⟨(h₁.sPoly hr).1, range_of (eta_le hF) (h₁.sPoly hr) (h₁.small r hr)⟩,
        ⟨(h₂.sPoly hr).1, range_of (eta_le hF) (h₂.sPoly hr) (h₂.small r hr)⟩⟩
  unfold packS
  exact bpAt_tr hP.bitPack (kgOk p) (packS_chk hF hr) (bpOk_eta hF) fun x y h =>
    ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem packS_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {r : Nat}
    (hr : r < p.ℓ + p.k) : Piece p S' (KRx p r 0 0) (KRx p (r + 1) 0 0) (packS P p r) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (packS_ok hP hF hp hr h) fun _ h => ⟨A, S, R, h⟩, packS_tr hP hF hr⟩

/-! ## `NTT` of `s₁` -/

theorem nttS_chk {p : Params} (hF : PFacts p) {j : Nat} (hj : j < p.ℓ) :
    ipChk kgR (kgW p) (sP p j) (sc oSS) = true := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  unfold ipChk; lay

theorem nttS_ok {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {σ : State}
    (hp : kgPre p S' σ) {j : Nat} (hj : j < p.ℓ) {A : Nat → Poly} {S : Nat → IPoly} {R : BitVec 64} {s : State}
    (h : KR p σ A S R (p.ℓ + p.k) j 0 s) : WP isa (nttS P p j) s (KR p σ A S R (p.ℓ + p.k) (j + 1) 0) := by
  have hkl := hF.kl; have hl := hF.l; have hk := hF.k; have hsc := scr_eq p
  have L := h.kc.lay hF hp
  have hS := h.s1 j hj
  rw [ifn (Nat.lt_irrefl j)] at hS
  unfold nttS nttAt
  refine WP.mono (ipAt_ok (t := ntt) hP.s64 hP.ntt L (nttS_chk hF hj) hS.1) fun s' ⟨hP', x', hb⟩ => ?_
  rcases hF.eta with ⟨_, hlen⟩ | ⟨_, hlen⟩ <;>
  exact ⟨h.kc.step hF hp hP' (by unfold kcChk; lay [hF.pk, hF.sk, hlen]), x'.trans h.x24, h.good,
    h.small, fun e he => L.keepPoly hP' (by lay [hF.pk, hF.sk, hlen]) (h.aS e he),
    fun i hi => L.keepPoly hP' (by lay [hF.pk, hF.sk, hlen]) (h.s2 i hi),
    fun j' hj' => if e : j' = j then by
        subst e; rw [ifp (Nat.lt_succ_self j'), hP'.pa (p := sP p j') (show Reg.x28 ∈ bases by decide), ← hS.2]
        exact hb
      else by
        have := L.keepPoly hP' (by lay [hF.pk, hF.sk, hlen]) (h.s1 j' hj')
        by_cases hlt : j' < j
        · rwa [ifp hlt, ← ifp (show j' < j + 1 by omega) (ntt (toRq (S j'))) (toRq (S j'))] at this
        · rwa [ifn hlt, ← ifn (show ¬ j' < j + 1 by omega) (ntt (toRq (S j'))) (toRq (S j'))] at this,
    by rw [L.keepBytes hP' (by lay [hF.pk, hF.sk, hlen])]; exact h.pk0,
    by rw [L.keepBytes hP' (by lay [hF.pk, hF.sk, hlen])]; exact h.sk0,
    by rw [L.keepBytes hP' (by lay [hF.pk, hF.sk, hlen])]; exact h.sk1,
    fun r hr => by
      have : lenS p * r + lenS p ≤ lenS p * (p.ℓ + p.k) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      rw [L.keepBytes hP' (by lay [hF.pk, hF.sk, hlen])]; exact h.packs r hr,
    fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem nttS_tr {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {j : Nat} (hj : j < p.ℓ) :
    RelCT isa (R p S' (KRx p (p.ℓ + p.k) j 0)) (nttS P p j) fun _ _ => True := by
  refine rel_of (Q := fun x y => Two p S' x y ∧ Reduced x.mem (pa x (sP p j)) ∧ Reduced y.mem (pa y (sP p j))) ?_
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ => ⟨kc_two hF p₁ p₂ pub h₁.kc h₂.kc, (h₁.s1 j hj).1,
      (h₂.s1 j hj).1⟩
  unfold nttS nttAt
  exact ipAt_tr (t := ntt) hP.ntt (kgOk p) (nttS_chk hF hj) fun x y h => ⟨h.1.lx, h.1.ly, h.2.1, h.2.2, h.1.same⟩

theorem nttS_piece {P : Prims} {S' : Nat} (hP : PrimsOk P S') {p : Params} (hF : PFacts p) {j : Nat}
    (hj : j < p.ℓ) : Piece p S' (KRx p (p.ℓ + p.k) j 0) (KRx p (p.ℓ + p.k) (j + 1) 0) (nttS P p j) :=
  ⟨fun _ _ hp ⟨A, S, R, h⟩ => WP.mono (nttS_ok hP hF hp hj h) fun _ h => ⟨A, S, R, h⟩, nttS_tr hP hF hj⟩

end VG.Proof.MlDsa.AArch64.KeyGen
