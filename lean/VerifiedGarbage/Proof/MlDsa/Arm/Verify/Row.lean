import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Compute

/-!
# ML-DSA verification on 32-bit ARM: the rows of `w′₁`

Row `r`: the sum of the products `Â[r, s] ẑ[s]` in `W` (polynomial 18),
`t̂₁[r]` unpacked from the public key (polynomial 16) and in the NTT domain,
`ĉ t̂₁[r]` (polynomial 17) subtracted from the sum, `NTT⁻¹` of it, `w′₁[r]`
(polynomial 19) by `UseHint`, and its `SimpleBitPack` to `B` (`row_piece`).
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee ip_ok ip_tr
  mul_ok mul_tr mulAdd_ok mulAdd_tr sub_ok sub_tr MulOk AccOk T1Ok t1_ok t1_tr UhOk uh_ok uh_tr SbpOk sbp_ok sbp_tr
  polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (seqR)
open VG.Spec.MlDsa (Params HintIs PolyIs NatPolyIs toRq polyAt natPolyAt coeffAt Reduced ntt nttInv multiplyNTT sub
  simpleBitPack useHint ofInt simpleBitUnpack t1Max d n q)
open VG.Proof.MlDsa.Verify (vZ zHat w1Row wRow dotAcc t1Hat vT1)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-- The polynomial `j` of the working space is `f`. -/
abbrev PIs (p : Params) (STK : Nat) (σ : State) (j : Nat) (f : Spec.MlDsa.Poly) (s : State) : Prop :=
  PolyIs s.mem ((vlay p STK σ).A 0 (oP j)) f

/-- In row `r`, with `f` holding of the memory. -/
abbrev RowI (p : Params) (STK : Nat) (r : Nat)
    (f : State → (Nat → Nat → Spec.MlDsa.Poly) → Spec.MlDsa.Poly → List (Vector Bool n) → State → Prop)
    (σ s : State) : Prop :=
  ∃ A' cc h R, KC5 p STK σ A' cc h R p.ℓ true r s ∧ f σ A' cc h s

/-- `t₁[r]` unpacked. -/
abbrev t1Raw (pk : List Byte) (r : Nat) : Spec.MlDsa.Poly := (vT1 pk r).map fun c => ofInt (c * 2 ^ d : Nat)

theorem KC5.aR {p : Params} {STK : Nat} {σ : State} {A' cc h R nz nc nr} {s : State}
    (hk : KC5 p STK σ A' cc h R nz nc nr s) {r j : Nat} (hr : r < p.k) (hj : j < p.ℓ) :
    PIs p STK σ (20 + 8 * r + j) (A' r j) s := hk.a r hr j hj

theorem KC5.zR {p : Params} {STK : Nat} {σ : State} {A' cc h R nc nr} {s : State}
    (hk : KC5 p STK σ A' cc h R p.ℓ nc nr s) {j : Nat} (hj : j < p.ℓ) :
    PIs p STK σ (8 + j) (zHat p (sgOf p σ) j) s := by
  have := hk.z j hj; rwa [ifp hj] at this

theorem KC5.cR {p : Params} {STK : Nat} {σ : State} {A' cc h R nr} {s : State}
    (hk : KC5 p STK σ A' cc h R p.ℓ true nr s) : PIs p STK σ 15 (ntt cc) s := by
  have := hk.c; rwa [ifp rfl] at this

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
  {r : Nat} (hr : r < p.k)
include hP hF hS hr

/-! ## `W = Σₛ Â[r, s] ẑ[s]` -/

omit hP hS in
theorem mulW_m {σ : State} {j : Nat} (hj : j < p.ℓ) : MulOk (vlay p STK σ) vWb pW (pA r j) (pZ j) := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide, by vsep hF,
    by vsep hF⟩

theorem mulW_piece :
    VPiece p STK (KX p STK p.ℓ true r) (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r 1))
      (mulAt P pW (pA r 0) (pZ 0)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5⟩ => ?_, ?_⟩
  · have ha := hk5.aR hr (j := 0) (by omega)
    have hz := hk5.zR (j := 0) (by omega)
    refine mul_ok hP.mul hk5.vc.site (by omega) (mulW_m hF hr (by omega)) ha.1 hz.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF), ?_⟩
    show PolyIs s'.mem (lpa (vlay p STK σ) pW) _
    rw [show dotAcc p (sgOf p σ) A' r 1 = _ from Proof.MlDsa.Verify.add_zero_left _]
    have e1 : polyAt s.mem (lpa (vlay p STK σ) (pA r 0)) = A' r 0 := ha.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) (pZ 0)) = zHat p (sgOf p σ) 0 := hz.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) (pA r 0)) ∧ Reduced x.mem (lpa (vlay p STK σ) (pZ 0))) ∧
      (Reduced y.mem (lpa (vlay p STK σ) (pA r 0)) ∧ Reduced y.mem (lpa (vlay p STK σ) (pZ 0))))
      (RelCT.exists_ fun σ => mul_tr hP.mul (by omega) (mulW_m hF (σ := σ) hr (by omega))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => ?_
    have a₂ : Reduced _ (lpa (vlay p STK _) (pA r 0)) := (h₂.aR hr (j := 0) (by omega)).1
    have z₂ : Reduced _ (lpa (vlay p STK _) (pZ 0)) := (h₂.zR (j := 0) (by omega)).1
    rw [← vlay_pub pub] at a₂ z₂
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨(h₁.aR hr (j := 0) (by omega)).1, (h₁.zR (j := 0) (by omega)).1⟩, ⟨a₂, z₂⟩⟩

theorem mulAddW_piece {j : Nat} (hj : j < p.ℓ) :
    VPiece p STK (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r j))
      (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r (j + 1)))
      (mulAddAt P pW (pA r j) (pZ j)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · have ha := hk5.aR hr hj
    have hz := hk5.zR hj
    refine mulAdd_ok hP.mulAdd hk5.vc.site (by omega) (mulW_m hF hr hj) hw.1 ha.1 hz.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF), ?_⟩
    show PolyIs s'.mem (lpa (vlay p STK σ) pW) _
    have e0 : polyAt s.mem (lpa (vlay p STK σ) pW) = dotAcc p (sgOf p σ) A' r j := hw.2
    have e1 : polyAt s.mem (lpa (vlay p STK σ) (pA r j)) = A' r j := ha.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) (pZ j)) = zHat p (sgOf p σ) j := hz.2
    rw [e0, e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced x.mem (lpa (vlay p STK σ) (pA r j)) ∧
        Reduced x.mem (lpa (vlay p STK σ) (pZ j))) ∧
      (Reduced y.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) (pA r j)) ∧
        Reduced y.mem (lpa (vlay p STK σ) (pZ j))))
      (RelCT.exists_ fun σ => mulAdd_tr hP.mulAdd (by omega) (mulW_m hF (σ := σ) hr hj)
        fun x y ⟨T, ⟨a, b, c⟩, ⟨d, e, f⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d, e, f⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    have a₂ : Reduced _ (lpa (vlay p STK _) (pA r j)) := (h₂.aR hr hj).1
    have z₂ : Reduced _ (lpa (vlay p STK _) (pZ j)) := (h₂.zR hj).1
    rw [← vlay_pub pub] at w₂' a₂ z₂
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨w₁.1, (h₁.aR hr hj).1, (h₁.zR hj).1⟩, ⟨w₂', a₂, z₂⟩⟩

theorem dot_piece :
    VPiece p STK (KX p STK p.ℓ true r) (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ))
      (dot P p r) := by
  have hl := hF.l
  unfold dot
  refine (mulW_piece hP hF hS hr).seq (Piece.mono (Piece.seqR
    (I := fun j => RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r j)) (p.ℓ - 1) 1
    fun j h1 h2 => mulAddW_piece hP hF hS hr (by omega)) (fun _ _ _ h => h) fun _ _ _ h => ?_)
  rwa [show 1 + (p.ℓ - 1) = p.ℓ by omega] at h

/-! ## `t̂₁[r]` -/

/-- After `t₁[r]`. -/
abbrev F2 (p : Params) (STK r : Nat) (t : State → Spec.MlDsa.Poly) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly)
    (_cc : Spec.MlDsa.Poly) (_h : List (Vector Bool n)) (s : State) : Prop :=
  PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ) s ∧ PIs p STK σ 16 (t σ) s

omit hP hS in
theorem t1_m {σ : State} : T1Ok (vlay p STK σ) vWb (.r4, 32 + 320 * r) pT := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide, by vsep hF⟩

theorem t1_piece :
    VPiece p STK (RowI p STK r fun σ A' _ _ => PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ))
      (RowI p STK r (F2 p STK r fun σ => t1Raw (pkOf p σ) r)) (unpackT1At P (.r4, 32 + 320 * r) pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold unpackT1At
    refine t1_ok hP.unpackT1 hk5.vc.site (by omega) (t1_m hF hr) fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e : bytesAt s.mem (lpa (vlay p STK σ) (.r4, 32 + 320 * r)) 320 =
        ((pkOf p σ).drop (32 + 320 * r)).take 320 := pk_slice hk5.vc (by rw [hF.pk]; omega)
    rw [e] at hb
    exact hb
  · unfold unpackT1At
    exact rel_of (RelCT.exists_ fun σ => t1_tr hP.unpackT1 (by omega) (t1_m hF (σ := σ) hr) fun x y h => h)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => ⟨σ₁, vc_twoL pub h₁.vc h₂.vc⟩

omit hP hS hr in
theorem nttT_m {σ : State} : PtrIn (vlay p STK σ) pT 1024 ∧ PtrIn (vlay p STK σ) (sc oSS) 1024 ∧
    sepB (vlay p STK σ).sizes (tri pT 1024) (tri (sc oSS) 1024) = true := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, by vsep hF⟩

theorem nttT_piece :
    VPiece p STK (RowI p STK r (F2 p STK r fun σ => t1Raw (pkOf p σ) r))
      (RowI p STK r (F2 p STK r fun σ => t1Hat (pkOf p σ) r)) (nttAt P pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · obtain ⟨m1, m2, m3⟩ := nttT_m hF (STK := STK) (σ := σ)
    unfold nttAt
    refine ip_ok (t := ntt) hP.ntt hk5.vc.site (by omega) m1 m2 (show ix Reg.r7 ∈ vWb by decide)
      (show ix Reg.r7 ∈ vWb by decide) m3 ht.1 fun s' k' hb => ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e : polyAt s.mem (lpa (vlay p STK σ) pT) = t1Raw (pkOf p σ) r := ht.2
    rw [e] at hb
    exact hb
  · unfold nttAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) pT) ∧ Reduced y.mem (lpa (vlay p STK σ) pT))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := nttT_m hF (STK := STK) (σ := σ)
        exact ip_tr (t := ntt) hP.ntt (by omega) m1 m2 (show ix Reg.r7 ∈ vWb by decide)
          (show ix Reg.r7 ∈ vWb by decide) m3 fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _, t₁⟩ ⟨_, _, _, _, h₂, _, t₂⟩ => ?_
    have t₂' : Reduced _ (lpa (vlay p STK _) pT) := t₂.1
    rw [← vlay_pub pub] at t₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, t₁.1, t₂'⟩

/-! ## `W = NTT⁻¹(W - ĉ t̂₁[r])` -/

/-- After `ĉ t̂₁[r]`. -/
abbrev F4 (p : Params) (STK r : Nat) (σ : State) (A' : Nat → Nat → Spec.MlDsa.Poly) (cc : Spec.MlDsa.Poly)
    (_h : List (Vector Bool n)) (s : State) : Prop :=
  PIs p STK σ 18 (dotAcc p (sgOf p σ) A' r p.ℓ) s ∧ PIs p STK σ 17 (multiplyNTT (ntt cc) (t1Hat (pkOf p σ) r)) s

omit hP hS hr in
theorem mulT_m {σ : State} : MulOk (vlay p STK σ) vWb pT2 pC pT := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide, by vsep hF,
    by vsep hF⟩

theorem mulT_piece :
    VPiece p STK (RowI p STK r (F2 p STK r fun σ => t1Hat (pkOf p σ) r)) (RowI p STK r (F4 p STK r))
      (mulAt P pT2 pC pT) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · have hc := hk5.cR
    refine mul_ok hP.mul hk5.vc.site (by omega) (mulT_m hF) hc.1 ht.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF),
        polyIs_keepW hk5.vc.site.ok k'.frame (by vsep hF) (by decide) rfl hw, ?_⟩
    have e1 : polyAt s.mem (lpa (vlay p STK σ) pC) = ntt cc := hc.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) pT) = t1Hat (pkOf p σ) r := ht.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) pC) ∧ Reduced x.mem (lpa (vlay p STK σ) pT)) ∧
      (Reduced y.mem (lpa (vlay p STK σ) pC) ∧ Reduced y.mem (lpa (vlay p STK σ) pT)))
      (RelCT.exists_ fun σ => mul_tr hP.mul (by omega) (mulT_m hF (σ := σ))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, _, t₁⟩ ⟨_, _, _, _, h₂, _, t₂⟩ => ?_
    have c₂ : Reduced _ (lpa (vlay p STK _) pC) := h₂.cR.1
    have t₂' : Reduced _ (lpa (vlay p STK _) pT) := t₂.1
    rw [← vlay_pub pub] at c₂ t₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨h₁.cR.1, t₁.1⟩, ⟨c₂, t₂'⟩⟩

omit hP hS hr in
theorem subW_m {σ : State} : AccOk (vlay p STK σ) vWb pW pT2 := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide, by vsep hF⟩

theorem subW_piece :
    VPiece p STK (RowI p STK r (F4 p STK r))
      (RowI p STK r fun σ A' cc _ => PIs p STK σ 18
        (sub (dotAcc p (sgOf p σ) A' r p.ℓ) (multiplyNTT (ntt cc) (t1Hat (pkOf p σ) r))))
      (subAt P pW pT2) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw, ht⟩ => ?_, ?_⟩
  · refine sub_ok hP.sub hk5.vc.site (by omega) (subW_m hF) hw.1 ht.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF), ?_⟩
    have e1 : polyAt s.mem (lpa (vlay p STK σ) pW) = dotAcc p (sgOf p σ) A' r p.ℓ := hw.2
    have e2 : polyAt s.mem (lpa (vlay p STK σ) pT2) = _ := ht.2
    rw [e1, e2] at hb
    exact hb
  · refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced x.mem (lpa (vlay p STK σ) pT2)) ∧
      (Reduced y.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) pT2)))
      (RelCT.exists_ fun σ => sub_tr hP.sub (by omega) (subW_m hF (σ := σ))
        fun x y ⟨T, ⟨a, b⟩, ⟨c, d⟩⟩ => ⟨T.1, T.2.1, T.2.2, a, b, c, d⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁, t₁⟩ ⟨_, _, _, _, h₂, w₂, t₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    have t₂' : Reduced _ (lpa (vlay p STK _) pT2) := t₂.1
    rw [← vlay_pub pub] at w₂' t₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, ⟨w₁.1, t₁.1⟩, ⟨w₂', t₂'⟩⟩

omit hP hS hr in
theorem invW_m {σ : State} : PtrIn (vlay p STK σ) pW 1024 ∧ PtrIn (vlay p STK σ) (sc oSS) 1024 ∧
    sepB (vlay p STK σ).sizes (tri pW 1024) (tri (sc oSS) 1024) = true := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, by vsep hF⟩

theorem invW_piece :
    VPiece p STK (RowI p STK r fun σ A' cc _ => PIs p STK σ 18
        (sub (dotAcc p (sgOf p σ) A' r p.ℓ) (multiplyNTT (ntt cc) (t1Hat (pkOf p σ) r))))
      (RowI p STK r fun σ A' cc _ => PIs p STK σ 18 (wRow p (pkOf p σ) (sgOf p σ) A' (ntt cc) r))
      (invNttAt P pW) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · obtain ⟨m1, m2, m3⟩ := invW_m hF (STK := STK) (σ := σ)
    unfold invNttAt
    refine ip_ok (t := nttInv) hP.invNtt hk5.vc.site (by omega) m1 m2 (show ix Reg.r7 ∈ vWb by decide)
      (show ix Reg.r7 ∈ vWb by decide) m3 hw.1 fun s' k' hb => ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF), ?_⟩
    have e : polyAt s.mem (lpa (vlay p STK σ) pW) = _ := hw.2
    rw [e] at hb
    exact hb
  · unfold invNttAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) pW))
      (RelCT.exists_ fun σ => by
        obtain ⟨m1, m2, m3⟩ := invW_m hF (STK := STK) (σ := σ)
        exact ip_tr (t := nttInv) hP.invNtt (by omega) m1 m2 (show ix Reg.r7 ∈ vWb by decide)
          (show ix Reg.r7 ∈ vWb by decide) m3 fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    rw [← vlay_pub pub] at w₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, w₁.1, w₂'⟩

/-! ## `w′₁[r]`, packed to `B` -/

omit hP hS in
theorem uh_m {σ : State} : UhOk (vlay p STK σ) vWb (pH r) pW p.γ₂ pW1 := by
  have hk := hF.k
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide, by vsep hF,
    by vsep hF, hF.g2.1, hF.g2.2⟩

omit hP hF hS in
theorem hint_row {σ : State} {m : Mem} {h : List (Vector Bool n)}
    (hh : HintIs m ((vlay p STK σ).A 0 (oP 0)) p.k h) :
    (Spec.MlDsa.hintAt m (lpa (vlay p STK σ) (pH r)) 1).headD (Vector.replicate n false) =
      h.getD r (Vector.replicate n false) := by
  have e : lpa (vlay p STK σ) (pH r) = (vlay p STK σ).A 0 (oP 0) + BitVec.ofNat 64 (1024 * r) := by
    show (vlay p STK σ).A 0 (oP r) = _
    rw [Lay.A, Lay.A, add_ofNat_add, show oP 0 + 1024 * r = oP r by simp only [oP]]
  rw [e]
  exact Proof.MlDsa.Verify.hintAt_row hh hr

theorem uh_piece :
    VPiece p STK (RowI p STK r fun σ A' cc _ => PIs p STK σ 18 (wRow p (pkOf p σ) (sgOf p σ) A' (ntt cc) r))
      (RowI p STK r fun σ A' cc h s => NatPolyIs s.mem ((vlay p STK σ).A 0 (oP 19))
        (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r))
      (useHintAt P (pH r) pW p.γ₂ pW1) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold useHintAt
    refine uh_ok hP.useHint hk5.vc.site (by omega) (uh_m hF hr) hw.1 fun s' k' hb =>
      ⟨A', cc, h, R, hk5.keep hF k' (by k5chk hF), ?_⟩
    have e : polyAt s.mem (lpa (vlay p STK σ) pW) = _ := hw.2
    rw [e, hint_row hr hk5.hint] at hb
    exact hb
  · unfold useHintAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      Reduced x.mem (lpa (vlay p STK σ) pW) ∧ Reduced y.mem (lpa (vlay p STK σ) pW))
      (RelCT.exists_ fun σ => uh_tr hP.useHint (by omega) (uh_m hF (σ := σ) hr)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : Reduced _ (lpa (vlay p STK _) pW) := w₂.1
    rw [← vlay_pub pub] at w₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, w₁.1, w₂'⟩

omit hP hS in
theorem sbpW_m {σ : State} : SbpOk (vlay p STK σ) vWb pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p) := by
  have hk := hF.k
  rcases hF.w1l with e | ⟨e, _⟩ <;>
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF [e]⟩, show ix Reg.r7 ∈ vWb by decide, by vsep hF [e],
    hF.sbp.1, hF.sbp.2.1⟩

omit hP hS hr in
theorem w1_bound {σ : State} {m : Mem} {a : Addr} {A' : Nat → Nat → Spec.MlDsa.Poly} {ch : Spec.MlDsa.Poly}
    {h : List (Vector Bool n)} {r : Nat} (h1 : NatPolyIs m a (w1Row p (pkOf p σ) (sgOf p σ) A' ch h r)) :
    ∀ i < n, (coeffAt m a i).toNat ≤ w1Max p := fun i hi => by
  rw [show (coeffAt m a i).toNat = (w1Row p (pkOf p σ) (sgOf p σ) A' ch h r)[i]'hi from by
    rw [← h1]; simp only [natPolyAt, Vector.getElem_ofFn]]
  simp only [w1Row, Vector.getElem_zipWith]
  exact Proof.MlDsa.Verify.useHint_le hF.g2.1 _ _

theorem sbpW_piece :
    VPiece p STK (RowI p STK r fun σ A' cc h s => NatPolyIs s.mem ((vlay p STK σ).A 0 (oP 19))
        (w1Row p (pkOf p σ) (sgOf p σ) A' (ntt cc) h r))
      (KX p STK p.ℓ true (r + 1)) (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p)) := by
  have hk := hF.k; have hl := hF.l
  refine ⟨fun σ s _ ⟨A', cc, h, R, hk5, hw⟩ => ?_, ?_⟩
  · unfold sbpAt
    refine sbp_ok hP.simpleBitPack hk5.vc.site (by omega) (sbpW_m hF hr) (w1_bound hF hw) fun s' k' hb =>
      ⟨A', cc, h, R, ?_⟩
    have hk' := hk5.keep hF k' (by k5chk hF)
    refine ⟨hk'.vc, hk'.hh, hk'.hint, hk'.a, hk'.z, hk'.c, fun r' hr' => ?_, hk'.r11, hk'.gd⟩
    rcases (by omega : r' < r ∨ r' = r) with hr' | rfl
    · exact hk'.rows r' hr'
    · show bytesAt s'.mem (lpa (vlay p STK σ) (sc (oB + w1Len p * r'))) (w1Len p) = _
      rw [hb]
      exact congrArg (simpleBitPack · (w1Max p)) hw
  · unfold sbpAt
    refine rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      (∀ i < n, (coeffAt x.mem (lpa (vlay p STK σ) pW1) i).toNat ≤ w1Max p) ∧
      (∀ i < n, (coeffAt y.mem (lpa (vlay p STK σ) pW1) i).toNat ≤ w1Max p))
      (RelCT.exists_ fun σ => sbp_tr hP.simpleBitPack (by omega) (sbpW_m hF (σ := σ) hr)
        fun x y ⟨T, a, b⟩ => ⟨T.1, T.2.1, T.2.2, a, b⟩)
      fun σ₁ _ _ _ _ _ pub ⟨_, _, _, _, h₁, w₁⟩ ⟨_, _, _, _, h₂, w₂⟩ => ?_
    have w₂' : ∀ i < n, (coeffAt _ (lpa (vlay p STK _) pW1) i).toNat ≤ w1Max p := w1_bound hF w₂
    rw [← vlay_pub pub] at w₂'
    exact ⟨σ₁, vc_twoL pub h₁.vc h₂.vc, w1_bound hF w₁, w₂'⟩

theorem row_piece : VPiece p STK (KX p STK p.ℓ true r) (KX p STK p.ℓ true (r + 1)) (row P p r) :=
  (dot_piece hP hF hS hr).seq ((t1_piece hP hF hS hr).seq ((nttT_piece hP hF hS hr).seq
    ((mulT_piece hP hF hS hr).seq ((subW_piece hP hF hS hr).seq ((invW_piece hP hF hS hr).seq
      ((uh_piece hP hF hS hr).seq (sbpW_piece hP hF hS hr)))))))

end

end VG.Proof.MlDsa.Arm.Verify
