import VerifiedGarbage.Proof.MlDsa.Arm.Verify.Z

/-!
# ML-DSA verification on 32-bit ARM: the entries of `Â`

Untrusted: everything here is checked by Lean. Once the hint is well formed
and `z` small (`VB`): `ρ` to the seed, and each entry `Â[r, s]`,
`RejNTTPoly(ρ ‖ s ‖ r)`, masked by its result (`aOne_piece`): after the
entries before `(r, c)` in row order (`VS`), each is reduced, and `r11` is
1 if every sampler succeeded, with the entries those of the standard for
some bound, and 0 if one of them fails within the least bound.
-/

namespace VG.Proof.MlDsa.Arm.Verify

open VG VG.Arm VG.Arm.RegUpd VG.Proof.MlKem.Arm
open VG.Proof.MlDsa.Arm.KeyGen (Site OkW ix tri lpa scrLen PtrIn Piece Two Rel2 rel_of relInv Callee RnOk rn_ok
  rn_tr polyIs_keepW polyAt_keepW reduced_keepW bytes_keepW keepD setB_ok copyS andMask_ok masked_poly seedA_eq
  taint7)
open VG.Impl.MlDsa.Arm.Verify
open VG.Impl.MlDsa.Arm.KeyGen (and11 mask setB seqR sampled)
open VG.Impl.MlKem.Arm (copy)
open VG.Spec.MlDsa (Params HintIs PolyIs toRq polyAt normRq Reduced rejNTTPoly minBounds Outcome)
open VG.Proof.MlDsa.Verify (vZ vRho aSeed)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Spec.Sha3 (bytesAt)

/-! ## After the checks of the signature -/

/-- The hint well formed and `z` small, in memory. -/
structure VB (p : Params) (STK : Nat) (σ s : State) : Prop where
  vc : VC p STK σ s
  hint : ∃ h, hintOf p σ = some h ∧ HintIs s.mem ((vlay p STK σ).A 0 (oP 0)) p.k h
  z : ∀ i < p.ℓ, PolyIs s.mem ((vlay p STK σ).A 0 (oP (8 + i))) (toRq (vZ p (sgOf p σ) i))
  zok : zOk p σ p.ℓ = true

theorem VB.keep {p : Params} (hF : VFacts p) {STK : Nat} {σ s s' : State} (h : VB p STK σ s)
    {W : List (Nat × Nat × Nat)} (hk : Kept ((vlay p STK σ).RL W) s s') (hc : vcChk p STK W = true)
    (hh : sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP 0, 1024 * p.k) W = true)
    (hz : ∀ i < p.ℓ, sepAll [scrLen p, STK, p.pkLen, 64, p.sigLen] (0, oP (8 + i), 1024) W = true) :
    VB p STK σ s' := by
  have hL := h.vc.site.ok
  obtain ⟨hh', e, hi⟩ := h.hint
  exact ⟨h.vc.keep hk hc, ⟨hh', e, hintIs_keepW hL hk.frame hh (by decide) (by have := hF.k; omega) hi⟩,
    fun i hi' => polyIs_keepW hL hk.frame (hz i hi') (by decide) rfl (h.z i hi'), h.zok⟩

theorem VB.r11 {p : Params} {STK : Nat} {σ s : State} (h : VB p STK σ s) (v : BitVec 32) :
    VB p STK σ (s.setReg .r11 v) :=
  ⟨h.vc.r11 v, h.hint, h.z, h.zok⟩

/-- The entry `(r', s')` comes before `(r, c)`. -/
abbrev Dn (r c r' s' : Nat) : Prop := r' < r ∨ (r' = r ∧ s' < c)

/-- The address of `Â[r, s]`. -/
abbrev aA (p : Params) (STK : Nat) (σ : State) (r s : Nat) : Addr := (vlay p STK σ).A 0 (oP (20 + 8 * r + s))

/-- After the entries of `Â` before `(r, c)`. -/
structure VS (p : Params) (STK : Nat) (r c : Nat) (σ s : State) : Prop where
  vb : VB p STK σ s
  rho : bytesAt s.mem ((vlay p STK σ).A 0 oSB) 32 = vRho (pkOf p σ)
  red : ∀ r' s', s' < p.ℓ → Dn r c r' s' → Reduced s.mem (aA p STK σ r' s')
  ok : ∃ q : Bool, s.gpr .r11 = flag q ∧
    (q = true → ∀ r' s', s' < p.ℓ → Dn r c r' s' →
      ∃ b : Nat, rejNTTPoly b (aSeed (pkOf p σ) r' s') = some (polyAt s.mem (aA p STK σ r' s'))) ∧
    (q = false → ∃ r' s', s' < p.ℓ ∧ Dn r c r' s' ∧ rejNTTPoly minBounds.rejNTT (aSeed (pkOf p σ) r' s') = none)

theorem Dn.lt {r c r' s' : Nat} (hd : Dn r c r' s') (hs : s' < 8) (hc : c ≤ 8) : 8 * r' + s' < 8 * r + c ∧ r' ≤ r := by
  rcases hd with h | ⟨rfl, h⟩ <;> omega

theorem flag_and01 (q : Bool) {r : BitVec 32} (hr : r = 0 ∨ r = 1) : flag q &&& r = flag (q && decide (r = 1)) := by
  rcases hr with rfl | rfl <;> cases q <;> decide

section
variable {P : Prims} {S : Nat} (hP : VPrimsOk P S) {p : Params} (hF : VFacts p) {STK : Nat} (hS : S + 8 ≤ STK)
include hP hF hS

/-! ## `ρ` to the seed -/

omit hP hS in
theorem rho_ok {σ s : State} (h : VB p STK σ s) (h11 : s.gpr .r11 = 1) :
    WP isa (copy .r4 0 .r7 oSB 32) s (VS p STK 0 0 σ) := by
  have hk := hF.k; have hl := hF.l
  refine WP.mono (copyS h.vc.site (sb := .r4) (so := 0) (db := .r7) (dO := oSB) (len := 32) ⟨rfl, by vsep hF⟩
    ⟨rfl, by vsep hF⟩ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by vsep hF))
    fun s' ⟨k', b'⟩ => ⟨h.keep hF k' (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF), ?_,
      fun _ _ _ hd => absurd hd (by omega), ⟨true, by rw [k'.cs .r11 (by decide) (by decide), h11]; rfl,
        fun _ _ _ _ hd => absurd hd (by omega), fun h => absurd h (by decide)⟩⟩
  show bytesAt s'.mem (lpa (vlay p STK σ) (.r7, oSB)) 32 = _
  rw [b', show lpa (vlay p STK σ) (.r4, 0) = (vlay p STK σ).A 2 0 from rfl, pk_slice h.vc (by rw [hF.pk]; omega),
    List.drop_zero]
  rfl

/-! ## One entry -/

omit hP hS in
theorem rn_m {σ : State} {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) :
    RnOk (vlay p STK σ) vWb (sc oSB) (pS (20 + (8 * r + c))) (sc oSS) := by
  have hk := hF.k; have hl := hF.l
  exact ⟨⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, ⟨rfl, by vsep hF⟩, show ix Reg.r7 ∈ vWb by decide,
    show ix Reg.r7 ∈ vWb by decide, by vsep hF, by vsep hF, by vsep hF⟩

theorem aOne_ok {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) {σ s : State} (h : VS p STK r c σ s) :
    WP isa (aOne P (8 * r + c)) s (VS p STK r (c + 1) σ) := by
  have hk := hF.k; have hl := hF.l
  have hs := h.vb.vc.site
  have hL := hs.ok
  unfold aOne sampled
  have e8 : (8 * r + c) % 8 = c := by omega
  have e8' : (8 * r + c) / 8 = r := by omega
  rw [e8, e8']
  -- `s` and `r` to the seed
  refine WP.seq (WP.block_append (WP.mono (setB_ok hs (q := sc (oSB + 32)) ⟨rfl, by vsep hF⟩ (by decide)
    (by decide) c) fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSB + 33)) ⟨rfl, by vsep hF⟩
      (by decide) (by decide) r) fun s₂ ⟨k₂, b₂⟩ => ?_))
  have kv := (h.vb.keep hF k₁ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)).keep hF k₂
    (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have hseed : bytesAt s₂.mem ((vlay p STK σ).A 0 oSB) 34 = aSeed (pkOf p σ) r c := by
    have b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans h.rho)
    have b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSB + 32) (l := 1) (by vsep hF) (by decide) (by decide)
    rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
      add_ofNat_add, add_ofNat_add, show aSeed (pkOf p σ) r c = _ from seedA_eq (vRho (pkOf p σ)) r c,
      List.append_assoc]
    refine congrArg _ ?_
    have e1 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 32)) 1 = [BitVec.ofNat 8 c] := b₁'.trans b₁
    have e2 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 32 + 1)) 1 = [BitVec.ofNat 8 r] := b₂
    rw [e1, e2]; rfl
  have kept12 : ∀ r' s', s' < p.ℓ → Dn r c r' s' → polyAt s₂.mem (aA p STK σ r' s') = polyAt s.mem (aA p STK σ r' s') ∧
      (Reduced s.mem (aA p STK σ r' s') → Reduced s₂.mem (aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega) (by omega)
    exact
    ⟨(polyAt_keepW hL k₂.frame (by vsep hF) (by decide) rfl).trans (polyAt_keepW hL k₁.frame (by vsep hF) (by decide) rfl),
      fun hr' => reduced_keepW hL k₂.frame (by vsep hF) (by decide) rfl (reduced_keepW hL k₁.frame (by vsep hF)
        (by decide) rfl hr')⟩
  have h11₂ : s₂.gpr .r11 = s.gpr .r11 := by rw [k₂.cs .r11 (by decide) (by decide), k₁.cs .r11 (by decide) (by decide)]
  -- the call
  refine WP.seq (rn_ok hP.rejNtt kv.vc.site (by omega) (rn_m hF hr hc) fun s₃ k₃ hred hout => ?_)
  have hseed' : bytesAt s₂.mem (lpa (vlay p STK σ) (sc oSB)) 34 = _ := hseed
  rw [hseed'] at hout
  have hr01 := Proof.MlDsa.KeyGen.outcome_01 hout
  have kv₃ := kv.keep hF k₃ (by vsep hF [vcChk]) (by vsep hF) (fun i hi => by vsep hF)
  have kept3 : ∀ r' s', s' < p.ℓ → Dn r c r' s' → polyAt s₃.mem (aA p STK σ r' s') = polyAt s₂.mem (aA p STK σ r' s') ∧
      (Reduced s₂.mem (aA p STK σ r' s') → Reduced s₃.mem (aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega) (by omega)
    exact
    ⟨polyAt_keepW hL k₃.frame (by vsep hF) (by decide) rfl,
      fun hr' => reduced_keepW hL k₃.frame (by vsep hF) (by decide) rfl hr'⟩
  have rho₃ : bytesAt s₃.mem ((vlay p STK σ).A 0 oSB) 32 = vRho (pkOf p σ) :=
    (bytes_keepW hL k₃.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
      ((bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
        ((bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans h.rho))
  have h11₃ : s₃.gpr .r11 = s.gpr .r11 := by rw [k₃.cs .r11 (by decide) (by decide), h11₂]
  -- the result and the mask
  refine WP.mono (andMask_ok kv₃.vc.site (a := pS (20 + (8 * r + c))) ⟨rfl, by vsep hF⟩
    (show ix Reg.r7 ∈ vWb by decide) hr01) fun s₄ ⟨k₄, r₄, co⟩ => ?_
  obtain ⟨pi, p1, _⟩ := masked_poly hred co
  have kv₄ := (kv₃.r11 (s₃.gpr .r11 &&& s₃.gpr .r0)).keep hF k₄ (by vsep hF [vcChk]) (by vsep hF)
    (fun i hi => by vsep hF)
  have kept4 : ∀ r' s', s' < p.ℓ → Dn r c r' s' → polyAt s₄.mem (aA p STK σ r' s') = polyAt s₃.mem (aA p STK σ r' s') ∧
      (Reduced s₃.mem (aA p STK σ r' s') → Reduced s₄.mem (aA p STK σ r' s')) := fun r' s' hs' hd => by
    have := hd.lt (by omega) (by omega)
    exact
    ⟨polyAt_keepW hL k₄.frame (by vsep hF) (by decide) rfl,
      fun hr' => reduced_keepW hL k₄.frame (by vsep hF) (by decide) rfl hr'⟩
  have ea : lpa (vlay p STK σ) (pS (20 + (8 * r + c))) = aA p STK σ r c := by
    show (vlay p STK σ).A 0 (oP (20 + (8 * r + c))) = _
    rw [← Nat.add_assoc]
  rw [ea] at pi p1 hout
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  refine ⟨kv₄, (bytes_keepW hL k₄.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans rho₃,
    fun r' s' hs' hd => ?_, ⟨q && decide (s₃.gpr .r0 = 1), ?_, fun hq' r' s' hs' hd => ?_, fun hq' => ?_⟩⟩
  · have := hd.lt (by omega) (by omega)
    rcases (by omega : Dn r c r' s' ∨ (r' = r ∧ s' = c)) with hd | ⟨rfl, rfl⟩
    · exact (kept4 r' s' hs' hd).2 ((kept3 r' s' hs' hd).2 ((kept12 r' s' hs' hd).2 (h.red r' s' hs' hd)))
    · exact pi.1
  · rw [r₄, h11₃, hq, flag_and01 q hr01]
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hq'
    rcases (by omega : Dn r c r' s' ∨ (r' = r ∧ s' = c)) with hd | ⟨rfl, rfl⟩
    · obtain ⟨b, hb⟩ := hok hq'.1 r' s' hs' hd
      refine ⟨b, ?_⟩
      rw [(kept4 r' s' hs' hd).1, (kept3 r' s' hs' hd).1, (kept12 r' s' hs' hd).1]
      exact hb
    · rw [p1 hq'.2]
      rcases hout with ⟨_, b, hb⟩ | ⟨h0, _⟩
      · exact ⟨b.rejNTT, hb⟩
      · rw [h0] at hq'; exact absurd hq'.2 (by decide)
  · simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq'
    rcases hq' with hq' | hq'
    · obtain ⟨r', s', hs', hd, hn⟩ := hbad hq'
      exact ⟨r', s', hs', by omega, hn⟩
    · rcases hout with ⟨h1, _⟩ | ⟨_, hn⟩
      · exact absurd h1 hq'
      · exact ⟨r, c, hc, by omega, hn⟩

/-! ## Constant time -/

omit hP hF hS in
theorem vsetB2_taint : ∀ v < 8, ∀ w < 8, (VG.Arm.taint.check (Taint.ofRegs [.r7])
    (.block (setB (sc (oSB + 32)) v ++ setB (sc (oSB + 33)) w)) (.block [])).isSome = true := by decide +kernel

omit hP hF hS in
/-- The check is the same for every offset: its hint is computed once. -/
theorem vAndMask_taint : ∀ j < 128, (VG.Arm.taint.check (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc (oP j))))
    (VG.Taint.hintOf VG.Arm.taint (Taint.ofRegs [.r7]) (.seq (.block and11) (mask (sc 0))))).isSome = true := by
  decide +kernel

theorem aOne_two {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) (σ : State) :
    RelCT isa (fun x y => Two (vlay p STK σ) vWb STK x y ∧
      bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 32) (aOne P (8 * r + c))
      fun _ _ => True := by
  have hk := hF.k; have hl := hF.l
  unfold aOne sampled
  have e8 : (8 * r + c) % 8 = c := by omega
  have e8' : (8 * r + c) / 8 = r := by omega
  rw [e8, e8']
  let F := fun (x x' : State) => (∃ rs, Kept rs x x') ∧
    bytesAt x'.mem ((vlay p STK σ).A 0 oSB) 34 = bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 ++
      [BitVec.ofNat 8 c, BitVec.ofNat 8 r]
  have hF1 : ∀ x, Site (vlay p STK σ) vWb STK x →
      WP isa (.block (setB (sc (oSB + 32)) c ++ setB (sc (oSB + 33)) r)) x (F x) := fun x hs =>
    WP.block_append (WP.mono (setB_ok hs (q := sc (oSB + 32)) ⟨rfl, by vsep hF⟩ (by decide) (by decide) c)
      fun s₁ ⟨k₁, b₁⟩ => WP.mono (setB_ok (hs.kept k₁) (q := sc (oSB + 33)) ⟨rfl, by vsep hF⟩
        (by decide) (by decide) r) fun s₂ ⟨k₂, b₂⟩ => ⟨⟨_, (k₁.monoL (W' := [tri (sc (oSB + 32)) 1,
          tri (sc (oSB + 33)) 1]) (by simp)).trans (k₂.monoL (by simp))⟩, by
        have hL := hs.ok
        have b₁' := bytes_keepW hL k₂.frame (i := 0) (o := oSB + 32) (l := 1) (by vsep hF) (by decide) (by decide)
        have b₀ := (bytes_keepW hL k₂.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide)).trans
          (bytes_keepW hL k₁.frame (i := 0) (o := oSB) (l := 32) (by vsep hF) (by decide) (by decide))
        rw [show (34 : Nat) = 32 + 1 + 1 from rfl, Proof.MlKem.bytesAt_add, Proof.MlKem.bytesAt_add, b₀,
          add_ofNat_add, add_ofNat_add, List.append_assoc]
        refine congrArg _ ?_
        have e1 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 32)) 1 = [BitVec.ofNat 8 c] := b₁'.trans b₁
        have e2 : bytesAt s₂.mem ((vlay p STK σ).A 0 (oSB + 32 + 1)) 1 = [BitVec.ofNat 8 r] := b₂
        rw [e1, e2]; rfl⟩)
  refine RelCT.seq ((RelCT.wpDep (M := isa) (P := fun x y => Two (vlay p STK σ) vWb STK x y ∧
      bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 32)
    (taint7 (fun _ _ h => h.1) (vsetB2_taint _ (by omega) _ (by omega))) (F := F)
    fun x y h => ⟨hF1 x h.1.1, hF1 y h.1.2.1⟩).mono (fun _ _ h => h)
      (Q' := fun (x y : State) => Two (vlay p STK σ) vWb STK x y ∧
        bytesAt x.mem ((vlay p STK σ).A 0 oSB) 34 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 34)
      fun x' y' ⟨_, x, y, ⟨T, e32⟩, ⟨⟨_, kx⟩, bx⟩, ⟨⟨_, ky⟩, by'⟩⟩ =>
        ⟨⟨T.1.kept kx, T.2.1.kept ky, by rw [kx.sp, ky.sp]; exact T.2.2⟩, by rw [bx, by', e32]⟩) ?_
  have ok := fun x (hs : Site (vlay p STK σ) vWb STK x) =>
    rn_ok hP.rejNtt hs (by omega) (name := "vg_mldsa_rej_ntt_poly") (rn_m hF (σ := σ) hr hc)
      (Q := fun x' => ∃ rs, Kept rs x x') fun _ k _ _ => ⟨_, k⟩
  refine RelCT.seq (VG.Proof.MlDsa.Arm.KeyGen.RelCT.two (fun _ _ h => h.1) (rn_tr hP.rejNtt (by omega) (rn_m hF hr hc)
      fun x y h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩) fun x hs => ok x hs) ?_
  exact taint7 (fun _ _ h => h) (vAndMask_taint _ (by omega))

theorem aOne_piece {r c : Nat} (hr : r < p.k) (hc : c < p.ℓ) :
    VPiece p STK (VS p STK r c) (VS p STK r (c + 1)) (aOne P (8 * r + c)) :=
  ⟨fun _ _ _ h => aOne_ok hP hF hS hr hc h,
    rel_of (Q := fun x y => ∃ σ, Two (vlay p STK σ) vWb STK x y ∧
      bytesAt x.mem ((vlay p STK σ).A 0 oSB) 32 = bytesAt y.mem ((vlay p STK σ).A 0 oSB) 32)
      (RelCT.exists_ fun σ => aOne_two hP hF hS hr hc σ) fun σ₁ _ _ _ _ _ pub h₁ h₂ =>
        ⟨σ₁, vc_twoL pub h₁.vb.vc h₂.vb.vc, by rw [h₁.rho, vlay_pub pub, h₂.rho, pub.2.2.2.2.2.1]⟩⟩

/-! ## The rows -/

omit hP hF hS in
theorem VS.next {r : Nat} {σ s : State} (h : VS p STK r p.ℓ σ s) : VS p STK (r + 1) 0 σ s := by
  have e : ∀ r' s', s' < p.ℓ → (Dn (r + 1) 0 r' s' ↔ Dn r p.ℓ r' s') := fun r' s' hs => by
    simp only [Dn]; omega
  obtain ⟨q, hq, hok, hbad⟩ := h.ok
  exact ⟨h.vb, h.rho, fun r' s' hs hd => h.red r' s' hs ((e r' s' hs).mp hd),
    ⟨q, hq, fun hq' r' s' hs hd => hok hq' r' s' hs ((e r' s' hs).mp hd),
      fun hq' => let ⟨r', s', hs, hd, hn⟩ := hbad hq'; ⟨r', s', hs, (e r' s' hs).mpr hd, hn⟩⟩⟩

theorem aRow_piece {r : Nat} (hr : r < p.k) : VPiece p STK (VS p STK r 0) (VS p STK (r + 1) 0) (aRow P p r) := by
  have hl := hF.l
  unfold aRow
  refine Piece.mono (Piece.seqR (I := fun e σ s => VS p STK r (e - 8 * r) σ s) p.ℓ (8 * r)
    fun e h1 h2 => ?_) (fun σ s _ h => by simpa using h) fun σ s _ h => VS.next (by simpa using h)
  have := aOne_piece hP hF hS hr (c := e - 8 * r) (by omega)
  rw [show 8 * r + (e - 8 * r) = e by omega, show e - 8 * r + 1 = e + 1 - 8 * r by omega] at this
  exact this

theorem rows_piece : VPiece p STK (VS p STK 0 0) (VS p STK p.k 0) (seqR (aRow P p) 0 p.k) := by
  refine Piece.mono (Piece.seqR (I := fun r => VS p STK r 0) p.k 0 fun r _ hr => aRow_piece hP hF hS (by omega))
    (fun _ _ _ h => h) fun σ s _ h => ?_
  simpa using h

end

end VG.Proof.MlDsa.Arm.Verify
