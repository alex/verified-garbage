import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Cmp
import VerifiedGarbage.Proof.MlDsa.KeyGen.Rest

/-!
# ML-DSA verification on AArch64: `vg_mldsa44_verify`, `vg_mldsa65_verify`, `vg_mldsa87_verify`

`c̃′ = H(μ ‖ w1Encode(w′₁))` (`hash_vpiece`) and its comparison with `c̃`
(`cmp_vpiece`); the function, piece by piece (`verify_vpiece`): a malformed
hint returns 0 at once, a `z` too large after the norms, and otherwise `x24`
holds the result of the samplers and then of the comparison. For primitives
`P` that meet their contracts (`PrimsOk`), `verify P p` meets `verifyContract
p` (`verify_verified`): it is correct, and leaks only its inputs, which the
contract makes public.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64 VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params Poly IPoly toRq ntt polyAt Reduced PolyIs HintIs Bounds minBounds rejNTTPoly sampleInBall
  simpleBitPack verifyMu normRq normR)
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.KeyGen (ifp ifn)
open VG.Proof.MlDsa.Verify (w1Row aSeed)

/-- `verifyMu` of the inputs of a run from `σ`, with the bounds `b`. -/
abbrev vv (p : Params) (σ : State) (b : Bounds) : Option Bool := verifyMu p b (vPk p σ) (vMu σ) (vSig p σ)

/-- At the end, before the epilogue: the result in `x24`. -/
def VFin (p : Params) (σ s : State) : Prop :=
  VC p σ s ∧ ((s.gpr .x24 = 1 ∧ ∃ b, vv p σ b = some true) ∨ (s.gpr .x24 = 0 ∧ vv p σ minBounds ≠ some true))

theorem false_ne {p : Params} {σ : State} {b : Bounds} (h : vv p σ b = some false) : vv p σ minBounds ≠ some true :=
  fun hm => by
    have e₁ := Proof.MlDsa.Verify.verifyMu_mono (Proof.MlDsa.Verify.bmax_left b minBounds).rejNTT
      (Proof.MlDsa.Verify.bmax_left b minBounds).ball h
    have e₂ := Proof.MlDsa.Verify.verifyMu_mono (Proof.MlDsa.Verify.bmax_right b minBounds).rejNTT
      (Proof.MlDsa.Verify.bmax_right b minBounds).ball hm
    rw [e₁] at e₂
    cases e₂

/-! ## The hash -/

/-- `w1Encode(w′₁)`. -/
abbrev w1Enc (p : Params) (σ : State) (h : List (Vector Bool Spec.MlDsa.n)) (A' : Nat → Nat → Poly) (c0 : Poly) :
    List Byte :=
  (List.range p.k).flatMap fun r => simpleBitPack (w1Row p (vPk p σ) (vSig p σ) A' (ntt c0) h r) (w1Max p)

/-- After the hash. -/
abbrev SCH (p : Params) (σ s : State) : Prop :=
  ∃ h A' c0 q, SC p σ h A' c0 q p.ℓ true p.k s ∧
    bytesAt s.mem (pa s (sc oCT)) p.ctildeLen = Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen

/-- The input pieces of the hash. -/
abbrev hIns (p : Params) : List Impl.MlKem.AArch64.Piece :=
  [⟨.x26, 0, 64⟩, ⟨.x28, oP (p.k * p.ℓ + 0), p.k * w1Len p⟩]

theorem hash_chk {p : Params} (hF : VFacts p) : hashChk (vR p) (vW p) (hIns p) ⟨.x28, oCT, p.ctildeLen⟩ = true := by
  have := hF.k; have := hF.l; have := hF.kl; have := hF.scr; have := hF.ct.2; have := hF.w1
  unfold hashChk pieceChk; vlay

theorem hash_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r) →
      RelCT isa P ((shake256With keccak.callee) (hIns p) [⟨.x28, oCT, p.ctildeLen⟩]) fun _ _ => True := by
  intro P hr
  obtain ⟨hint, hh⟩ := keccak.mldsaVerifyHashTaint p hp
  exact VectorTaint.relRegs bases hr hh

theorem cmp_taint {p : Params} (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87) :
    ∀ {P : State → State → Prop}, (∀ x y, P x y → x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r) →
      RelCT isa P (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen) fun _ _ => True := by
  intro P hr
  rcases hp with rfl | rfl | rfl
  · exact taintRel bases hr (by taint_decide)
  · exact taintRel bases hr (by taint_decide)
  · exact taintRel bases hr (by taint_decide)

theorem flatMap_congr' {α β : Type} {f g : α → List β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h x (List.mem_cons_self ..),
      flatMap_congr' fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem rows_bytes {p : Params} {σ : State} {h : List (Vector Bool Spec.MlDsa.n)} {A' : Nat → Nat → Poly} {c0 : Poly}
    {q : Bool} {s : State} (hs : SC p σ h A' c0 q p.ℓ true p.k s) :
    Proof.MlKem.AArch64.pbytes s ⟨.x28, oP (p.k * p.ℓ + 0), p.k * w1Len p⟩ = w1Enc p σ h A' c0 := by
  show bytesAt s.mem (s.gpr .x28 + BitVec.ofNat 64 (oP (p.k * p.ℓ + 0))) (p.k * w1Len p) = _
  rw [show p.k * w1Len p = w1Len p * p.k from Nat.mul_comm _ _, Proof.MlDsa.KeyGen.bytesAt_pieces]
  exact flatMap_congr' fun r hr => hs.rows r (List.mem_range.mp hr)

theorem hash_vpiece {S : Nat} (h16 : 16 ≤ S) (hSl : S < 2 ^ 64) {p : Params} (hF : VFacts p) :
    VPiece p S (SCx p p.ℓ true p.k) (SCH p) ((shake256With keccak.callee) (hIns p) [⟨.x28, oCT, p.ctildeLen⟩]) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs⟩ => ?_, vrel_of (Q := VTwo p S) (hash_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ => vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  refine WP.mono (shake_ok h16 hSl L (by simp) (hash_chk hF)) fun s' ⟨hP', x', ho⟩ => ⟨h, A', c0, q, ?_, ?_⟩
  · exact hs.keep hF hp hP' (by have := hF.ct.2; scchk hF) x'
  · simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil] at ho
    rw [hP'.pa (show Reg.x28 ∈ keptRegs by decide), ho, rows_bytes hs]
    refine congrArg (Spec.MlDsa.H · p.ctildeLen) (congrArg (· ++ _) ?_)
    show bytesAt s.mem (s.gpr .x26 + BitVec.ofNat 64 0) 64 = _
    exact hs.vc.mu

/-! ## The comparison -/

theorem cmp_vpiece {S : Nat} {p : Params} (hF : VFacts p) :
    VPiece p S (SCH p) (VFin p) (cmpAnd (sc oCT) (.x27, 0) p.ctildeLen) := by
  refine ⟨fun σ s hp ⟨h, A', c0, q, hs, hH⟩ => ?_, vrel_of (Q := VTwo p S) (cmp_taint hF.mem fun x y h => h.bases)
    fun _ _ _ _ p₁ p₂ pub ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ => vc_two hF p₁ p₂ pub h₁.vc h₂.vc⟩
  have L := hs.vc.lay hF hp
  have := hF.ct.2; have := hF.sig; have := hF.scr; have := hF.k; have := hF.l; have := hF.kl
  refine WP.mono (cmpAnd_ok L (by omega) (by omega) (by vlay) (by vlay)) fun s' ⟨hP', x'⟩ => ⟨?_, ?_⟩
  · exact hs.vc.step hF hp hP' (by unfold vcChk; vlay)
  · rw [hH, ctOf_eq hF hs.vc, hs.x24] at x'
    have e : s'.gpr .x24 = flag (q = true ∧ Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ) := by
      rw [x', and_flag (P := q = true)
        (Q := Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ) _ (by split <;> rfl)]
    obtain ⟨hA1, hA0⟩ := hs.gd
    cases q with
    | false =>
      refine .inr ⟨by rw [e]; exact ifn (fun h => Bool.false_ne_true h.1) _ _, ?_⟩
      rcases hA0 rfl with ⟨r, hr, c, hc, hn'⟩ | hn'
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_rej_none minBounds _ _ hs.hh hr hc hn']; nofun
      · show verifyMu p minBounds _ _ _ ≠ some true
        rw [Proof.MlDsa.Verify.verifyMu_ball_none minBounds _ _ hs.hh (Option.map_eq_none_iff.mp hn')]; nofun
    | true =>
      obtain ⟨hA, hB⟩ := hA1 rfl
      obtain ⟨nA, hnA⟩ := Proof.MlDsa.Verify.common_bound (P := fun r n => ∀ c < p.ℓ,
          rejNTTPoly n (aSeed (vPk p σ) r c) = some (A' r c))
        (fun _ _ _ hle h c hc => Proof.MlDsa.Verify.rejNTTPoly_mono hle (h c hc)) p.k fun r hr =>
          Proof.MlDsa.Verify.common_bound (P := fun c n => rejNTTPoly n (aSeed (vPk p σ) r c) = some (A' r c))
            (fun _ _ _ hle h => Proof.MlDsa.Verify.rejNTTPoly_mono hle h) p.ℓ fun c hc =>
              let ⟨b, hb⟩ := hA r hr c hc; ⟨b.rejNTT, hb⟩
      obtain ⟨bB, hbB⟩ := hB
      obtain ⟨cc, hcc, hcc'⟩ := Option.map_eq_some_iff.mp hbB
      have hl : h.length = p.k := hs.hint.1
      have ev := Proof.MlDsa.Verify.verifyMu_rows p ⟨0, 0, nA, bB.ball⟩ (vPk p σ) (vMu σ) (vSig p σ) hs.hh hl hnA
        hcc
      rw [decide_eq_true ((Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1 _).mpr hs.nok), hcc', Bool.true_and,
        ← hF.g2.2] at ev
      by_cases hE : Spec.MlDsa.H (vMu σ ++ w1Enc p σ h A' c0) p.ctildeLen = ctOf p σ
      · exact .inl ⟨by rw [e]; exact ifp (show true = true ∧ _ from ⟨rfl, hE⟩) _ _, ⟨_, ev.trans (congrArg some (beq_iff_eq.mpr hE.symm))⟩⟩
      · exact .inr ⟨by rw [e]; exact ifn (fun h : true = true ∧ _ => hE h.2) _ _,
          false_ne (ev.trans (congrArg some (beq_eq_false_iff_ne.mpr (Ne.symm hE))))⟩

/-! ## The function -/

theorem compute_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (VB p) (VFin p) ((computeWith keccak.callee) P p) := by
  unfold computeWith
  refine VPiece.seq (J := SCx p p.ℓ false 0) ?_ ((nttC_vpiece hP hF).seq (VPiece.seq (J := SCx p p.ℓ true p.k) ?_
    ((hash_vpiece hP.s16 hP.s64 hF).seq (cmp_vpiece hF))))
  · refine VPiece.mono (VPiece.seqR (I := fun i => SCx p i false 0) p.ℓ 0 fun i _ hi => nttZ_vpiece hP hF (by omega))
      (fun _ _ _ h => vb_sc h) fun _ _ _ h => ?_
    simpa using h
  · refine VPiece.mono (VPiece.seqR (I := fun r => SCx p p.ℓ true r) p.k 0 fun r _ hr => row_vpiece hP hF (by omega))
      (fun _ _ _ h => h) fun _ _ _ h => ?_
    simpa using h

theorem normOk_zero (p : Params) (σ : State) : normOk p σ 0 := fun _ h => absurd h (Nat.not_lt_zero _)

theorem body_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s => VC p σ s ∧ s.gpr .x24 = 1) (VFin p) ((bodyWith keccak.callee) P p) := by
  unfold bodyWith
  refine (hint_vpiece hP hF).seq (VPiece.ifOk (T := fun σ => (hintOf p σ).isSome = true)
    (fun _ _ _ h => h.2.1) (fun _ _ _ _ pub => by rw [hintOf, hintOf, (vPub_eq pub).2.2.2.1]) ?_ ?_)
  · refine VPiece.seq (J := Z0 p p.ℓ) ?_ (VPiece.ifOk (T := fun σ => normOk p σ p.ℓ) (fun _ _ _ h => h.2)
      (fun _ _ _ _ pub => by simp only [normOk, zOf, (vPub_eq pub).2.2.2.1]) ((samples_vpiece hP hF).seq
        (compute_vpiece hP hF)) fun σ s _ h hn => ⟨h.1.vc, .inr ⟨by rw [h.2]; exact ifn hn _ _, ?_⟩⟩)
    · refine VPiece.mono (VPiece.seqR (I := fun j => Z0 p j) p.ℓ 0 fun j _ hj => zOne_vpiece hP hF (by omega))
        (fun σ s _ ⟨⟨hv, hx, hH⟩, ht⟩ => ⟨⟨hv, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩, ?_⟩) fun _ _ _ h => ?_
      · obtain ⟨hh, e⟩ := Option.isSome_iff_exists.mp ht
        exact ⟨hh, e, hH hh e⟩
      · rw [hx]; exact flag_congr (iff_of_true ht (normOk_zero p σ))
      · simpa using h
    · obtain ⟨hh, e, _⟩ := h.1.hint
      show verifyMu p minBounds _ _ _ ≠ some true
      exact Proof.MlDsa.Verify.verifyMu_norm minBounds _ _ e
        (by rw [Proof.MlDsa.Verify.normR_vZ_iff hF.g1.2.1 p hF.g1.1]; exact hn)
  · intro σ s _ h hn
    refine ⟨h.1, .inr ⟨by rw [h.2.1]; exact ifn hn _ _, ?_⟩⟩
    show verifyMu p minBounds _ _ _ ≠ some true
    rw [Proof.MlDsa.Verify.verifyMu_hint_none minBounds _ _ (Option.not_isSome_iff_eq_none.mp hn)]
    nofun

theorem epi_vpiece {S : Nat} {p : Params} (hF : VFacts p) :
    VPiece p S (VFin p) (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p AArch64.abi S).post σ s)
      (.block epi) := by
  refine ⟨fun σ s hp ⟨hv, hr⟩ => ?_, vrel_of (Q := VTwo p S) (taintRel [.x28] (fun x y h => h.x28)
    (by taint_decide)) fun _ _ _ _ p₁ p₂ pub h₁ h₂ => vc_two hF p₁ p₂ pub h₁.1 h₂.1⟩
  have L := hv.lay hF hp
  have hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48 := by
    have := L.inR (p := svP) (l := 48) (by have := hF.scr; have := hF.k; vlay)
    rwa [pa, hv.top.x28] at this
  refine WP.mono (epi_ok hv.top hin) fun s' ⟨ha, hx, _⟩ => ⟨ha, ?_⟩
  sig_post [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs]
  rcases hr with ⟨e, hb⟩ | ⟨e, hb⟩
  · exact .inl ⟨by rw [hx, e]; rfl, hb⟩
  · exact .inr ⟨by rw [hx, e]; rfl, hb⟩

theorem verify_vpiece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    VPiece p S (fun σ s => s = σ)
      (fun σ s => abiPreserved σ s ∧ (Spec.MlDsa.verifyContract p AArch64.abi S).post σ s) ((verifyWith keccak.callee) P p) :=
  (pro_vpiece hF).seq ((body_vpiece hP hF).seq (epi_vpiece hF))

/-- `vg_mldsa*_verify` of the parameter set `p` meets its contract, for any
verified implementations `P` of the primitives it calls that use at most `S`
bytes of stack, if the contract is satisfiable. -/
theorem verify_verified {P : Prims} {S : Nat} (hP : PrimsOk P S) (p : Params)
    (hp : p = Spec.MlDsa.mlDsa44 ∨ p = Spec.MlDsa.mlDsa65 ∨ p = Spec.MlDsa.mlDsa87)
    (hsat : ∃ s, (Spec.MlDsa.verifyContract p AArch64.abi S).pre s) :
    Verified AArch64.target ((verifyWith keccak.callee) P p) (Spec.MlDsa.verifyContract p AArch64.abi S) :=
  ⟨fun σ hσ => (verify_vpiece hP (vfacts hp)).ok σ σ hσ rfl,
    relStart (Q := fun _ _ => True) (verify_vpiece hP (vfacts hp)).tr, hsat⟩

end VG.Proof.MlDsa.AArch64.Verify
