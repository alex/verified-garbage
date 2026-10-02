import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample

/-!
# ML-DSA verification on x86-64: constant time, `w′₁`, the hash and the comparison

Untrusted: everything here is checked by Lean. Each run's invariant is
`SC` at the start of a row, with the facts after each step of it (`IRX`),
which give each call's trace the reduced inputs it needs.
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt useHint_le w1Row)

/-- Two runs whose states lie within the layout from states satisfying `T`. -/
theorem RV.lrelOf {p : Params} (hp : p ∈ params) {I : State → State → Prop}
    (hI : ∀ σ s, I σ s → ∃ s₀ W, T p σ s₀ ∧ PostB s₀ s W) {x y : State} (h : RV p I x y) :
    LRel (vR p) (vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩ := h
  obtain ⟨x₀, _, t₁, hx⟩ := hI _ _ i₁
  obtain ⟨y₀, _, t₂, hy⟩ := hI _ _ i₂
  exact ⟨(t₁.lay hp v₁).post hx, (t₂.lay hp v₂).post hy, (T.sameB pub t₁ t₂).post hx hy⟩

/-- While computing, before `ẑ` and `ĉ`, and at the start of row `r`. -/
def IC (p : Params) (j : Nat) (σ s : State) : Prop :=
  ∃ (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (q : Bool) (cH : Poly), SC p h A' (q = true) j cH 0 σ s
def IR (p : Params) (r : Nat) (σ s : State) : Prop :=
  ∃ (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (q : Bool) (cH : Poly), SC p h A' (q = true) p.ℓ cH r σ s

/-- In row `r`, after a piece: `F` of the state at the start of the row. -/
def IRX (p : Params) (r : Nat)
    (F : List (Vector Bool n) → (Nat → Nat → Poly) → Poly → State → State → State → Prop) (σ s : State) : Prop :=
  ∃ (h : List (Vector Bool n)) (A' : Nat → Nat → Poly) (q : Bool) (cH : Poly) (s₀ : State),
    SC p h A' (q = true) p.ℓ cH r σ s₀ ∧ F h A' cH σ s₀ s

section
variable {p : Params} {r : Nat}
  {F F' : List (Vector Bool n) → (Nat → Nat → Poly) → Poly → State → State → State → Prop}

theorem IRX.lrel (hp : p ∈ params) (hF : ∀ h A' cH σ s₀ s, F h A' cH σ s₀ s → ∃ W, PostB s₀ s W) {x y : State}
    (h : RV p (IRX p r F) x y) : LRel (vR p) (vW p) x y :=
  RV.lrelOf hp (fun _ _ ⟨_, _, _, _, s₀, hs, hf⟩ => let ⟨W, hW⟩ := hF _ _ _ _ _ _ hf; ⟨s₀, W, hs.t, hW⟩) h

theorem IRX.step {c : Prog isa}
    (hw : ∀ h A' (q : Bool) cH σ s₀ s, VPre p σ → SC p h A' (q = true) p.ℓ cH r σ s₀ → F h A' cH σ s₀ s →
      WP isa c s (F' h A' cH σ s₀))
    (ht : RelCT isa (RV p (IRX p r F)) c fun _ _ => True) : RelCT isa (RV p (IRX p r F)) c (RV p (IRX p r F')) :=
  relInv (fun σ s hv ⟨h, A', q, cH, s₀, hs, hf⟩ => WP.mono (hw h A' q cH σ s₀ s hv hs hf)
    fun _ h' => ⟨h, A', q, cH, s₀, hs, h'⟩) ht

end

/-! ## `ẑ` and `ĉ` -/

theorem nttZ_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {i : Nat} (hi : i < p.ℓ) :
    RelCT isa (RV p (IC p i)) (nttAt P (pZ i)) (RV p (IC p (i + 1))) := by
  have hc := nttChk_all p hp
  simp only [nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨c1, _⟩, _⟩ := hc.1.1 i hi
  have hT : ∀ σ s, IC p i σ s → T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (nttZ_ok C hp hv hi hs) fun _ h' => ⟨h, A', q, cH, h'⟩)
    (ipAt_tr C.ntt (layOk p hp) c1 fun x y hxy => ?_)
  have L := RV.lrel hp hT hxy
  obtain ⟨_, _, _, _, _, ⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := hxy
  exact ⟨L.1, L.2.1, (hx.z i hi).1, (hy.z i hi).1, L.2.2⟩

theorem nttC_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p (IC p p.ℓ)) (nttAt P pC) (RV p (IR p 0)) := by
  have hc := nttChk_all p hp
  simp only [nttChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨_, c1⟩, _⟩ := hc
  have hT : ∀ σ s, IC p p.ℓ σ s → T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (nttC_ok C hp hv hs) fun _ h' => ⟨h, A', q, _, h'⟩)
    (ipAt_tr C.ntt (layOk p hp) c1 fun x y hxy => ?_)
  have L := RV.lrel hp hT hxy
  obtain ⟨_, _, _, _, _, ⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := hxy
  exact ⟨L.1, L.2.1, hx.c.1, hy.c.1, L.2.2⟩

/-! ## A row -/

section Row
variable {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {r : Nat} (hr : r < p.k)
include C hp hr

theorem dot_tr : RelCT isa (RV p (IR p r)) (dot P p r)
    (RV p (IRX p r fun _ A' _ σ s₀ s => DI p σ A' r p.ℓ s₀ s)) := by
  have R := rowC hp hr
  obtain ⟨_, _, hZ, hA⟩ := keepC_spec R.keep
  have hT : ∀ σ s, IR p r σ s → T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  unfold dot
  refine RelCT.seq (relInv (I' := IRX p r fun _ A' _ σ s₀ s => DI p σ A' r 1 s₀ s)
    (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (dotFirst_ok C hp hv hr hs) fun _ h' => ⟨h, A', q, cH, s, hs, h'⟩)
    (mulAt_tr C.mul (layOk p hp) (R.mul 0 R.l1) fun x y hxy => ?_)) ?_
  · have L := RV.lrel hp hT hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, hx⟩, ⟨_, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, ⟨(hx.a r hr 0 R.l1).1, (hx.zHat R.l1).1⟩, ⟨(hy.a r hr 0 R.l1).1, (hy.zHat R.l1).1⟩, L.2.2⟩
  have hs := seqR_tr (R := fun j => RV p (IRX p r fun _ A' _ σ s₀ s => DI p σ A' r j s₀ s)) (p.ℓ - 1) 1
    fun k hk hk' => IRX.step (fun h A' q cH σ s₀ s hv hs hd => dotStep_ok C hp hv hr hs (by omega) hd)
      (mulAddAt_tr C.mulAdd (layOk p hp) (R.mul k (by omega)) fun x y hxy => ?_)
  · rwa [show 1 + (p.ℓ - 1) = p.ℓ by have := R.l1; omega] at hs
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hd => ⟨_, hd.1⟩) hxy
    have hz : k ≠ 100 := by have := kl_le p hp; omega
    have red : ∀ {σ s}, VPre p σ → IRX p r (fun _ A' _ σ s₀ s => DI p σ A' r k s₀ s) σ s →
        Reduced s.mem (pa s pW) ∧ Reduced s.mem (pa s (pA p.ℓ r k)) ∧ Reduced s.mem (pa s (pZ k)) :=
      fun hv ⟨_, _, _, _, s₀, hs, hP, _, hW⟩ => by
        have L₀ := hs.t.lay hp hv
        have H := hP.mono (sub1 (wsR_mem p r).1)
        exact ⟨by rw [pa_rbx hP]; exact hW.1, L₀.keepRed H (hA r hr k (by omega)) (hs.a r hr k (by omega)).1,
          L₀.keepRed H (hZ k (by omega) hz) (hs.zHat (by omega)).1⟩
    obtain ⟨_, _, v₁, v₂, _, i₁, i₂⟩ := hxy
    exact ⟨L.1, L.2.1, red v₁ i₁, red v₂ i₂, L.2.2⟩

omit C in
theorem RF7.bound {σ : State} {h : List (Vector Bool n)} {A' : Nat → Nat → Poly} {cH : Poly} {s₀ s : State}
    (hf : RF7 p σ h A' cH r s₀ s) : ∀ i < n, (coeffAt s.mem (pa s pW1) i).toNat ≤ w1Max p := fun i hi => by
  have R := rowC hp hr
  have hq₇ : natPolyAt s.mem (pa s pW1) = _ := hf.2
  have := congrArg (·[i]'hi) hq₇
  simp only [natPolyAt, Vector.getElem_ofFn, w1Row, Vector.getElem_zipWith] at this
  rw [this, R.max]
  exact useHint_le R.g2 _ _

theorem rowRest_tr : RelCT isa (RV p (IRX p r fun _ A' _ σ s₀ s => RF1 p σ A' r s₀ s))
    (.seq (unpackT1At P (.rbp, 32 + 320 * r) pT) (.seq (nttAt P pT) (.seq (mulAt P pT2 pC pT)
      (.seq (subAt P pW pT2) (.seq (invNttAt P pW) (.seq (useHintAt P (pH r) pW p.γ₂ pW1)
        (sbpAt P pW1 (w1Max p) (sc (oB + w1Len p * r)) (w1Len p))))))))
    fun _ _ => True := by
  have R := rowC hp hr
  have hS := layOk p hp
  refine RelCT.seq (IRX.step (F' := fun _ A' _ σ s₀ s => RF2 p σ A' r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => row1_ok C hp hv hr hs hf)
    (unpackT1At_tr C.unpackT1 hS R.t1 fun x y hxy => IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy)) ?_
  refine RelCT.seq (IRX.step (F' := fun _ A' _ σ s₀ s => RF3 p σ A' r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => row2_ok C hp hv hr hs hf)
    (ipAt_tr C.ntt hS R.ipT fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, hx.2.1, hy.2.1, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun _ A' cH σ s₀ s => RF4 p σ A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => row3_ok C hp hv hr hs hf)
    (mulAt_tr C.mul hS R.mulT fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1.1⟩) hxy
    have red : ∀ {σ s}, VPre p σ → IRX p r (fun _ A' _ σ s₀ s => RF3 p σ A' r s₀ s) σ s →
        Reduced s.mem (pa s pC) ∧ Reduced s.mem (pa s pT) := fun hv ⟨_, _, _, _, _, hs, hf⟩ =>
      ⟨(hs.t.lay hp hv).keepRed hf.1.1.1 R.keepC' hs.c.1, hf.2.1⟩
    obtain ⟨_, _, v₁, v₂, _, i₁, i₂⟩ := hxy
    exact ⟨L.1, L.2.1, red v₁ i₁, red v₂ i₂, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun _ A' cH σ s₀ s => RF5 p σ A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => row4_ok C hp hv hr hs hf)
    (subAt_tr C.sub hS R.sub fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, ⟨hx.1.2.1, hx.2.1⟩, ⟨hy.1.2.1, hy.2.1⟩, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun _ A' cH σ s₀ s => RF6 p σ A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => row5_ok C hp hv hr hs hf)
    (ipAt_tr C.invNtt hS R.ipW fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, hx.2.1, hy.2.1, L.2.2⟩
  refine RelCT.seq (IRX.step (F' := fun h A' cH σ s₀ s => RF7 p σ h A' cH r s₀ s)
    (fun h A' q cH σ s₀ s hv hs hf => row6_ok C hp hv hr hs hf)
    (useHintAt_tr C.useHint hS R.g2 R.uh fun x y hxy => ?_)) ?_
  · have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy
    obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
    exact ⟨L.1, L.2.1, hx.2.1, hy.2.1, L.2.2⟩
  refine sbpAt_tr C.simpleBitPack hS R.sbpB R.len R.sbp fun x y hxy => ?_
  have L := IRX.lrel hp (fun _ _ _ _ _ _ hf => ⟨_, hf.1.1⟩) hxy
  obtain ⟨_, _, _, _, _, ⟨_, _, _, _, _, _, hx⟩, ⟨_, _, _, _, _, _, hy⟩⟩ := hxy
  exact ⟨L.1, L.2.1, RF7.bound hp hr hx, RF7.bound hp hr hy, L.2.2⟩

theorem row_tr : RelCT isa (RV p (IR p r)) (row P p r) (RV p (IR p (r + 1))) := by
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (row_ok C hp hv hr hs) fun _ h' => ⟨h, A', q, cH, h'⟩) ?_
  unfold row
  exact RelCT.seq (RelCT.mono (dot_tr C hp hr) (fun _ _ h => h)
    fun _ _ ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, A₁, q₁, c₁, x₀, hx, dx⟩, ⟨h₂, A₂, q₂, c₂, y₀, hy, dy⟩⟩ =>
      ⟨σ₁, σ₂, v₁, v₂, pub, ⟨h₁, A₁, q₁, c₁, x₀, hx, DI.rf1 dx⟩, ⟨h₂, A₂, q₂, c₂, y₀, hy, DI.rf1 dy⟩⟩)
    (rowRest_tr C hp hr)

end Row

/-! ## The whole computation -/

theorem compute_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p (IC p 0)) (compute P p) (RV p (T p)) := by
  have hc := compChk_all p hp
  simp only [compChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨c1, _⟩, c3⟩, c4⟩, c5⟩, _⟩ := hc
  unfold compute
  have hz : RelCT isa (RV p (IC p 0)) (seqR (fun i => nttAt P (pZ i)) 0 p.ℓ) (RV p (IC p p.ℓ)) := by
    have := seqR_tr (R := fun i => RV p (IC p i)) p.ℓ 0 fun i _ hi => nttZ_tr C hp (by omega)
    rwa [Nat.zero_add] at this
  have hrows : RelCT isa (RV p (IR p 0)) (seqR (row P p) 0 p.k) (RV p (IR p p.k)) := by
    have := seqR_tr (R := fun r => RV p (IR p r)) p.k 0 fun r _ hr => row_tr C hp (by omega)
    rwa [Nat.zero_add] at this
  refine RelCT.seq hz (RelCT.seq (nttC_tr C hp) (RelCT.seq hrows ?_))
  have hT : ∀ σ s, IR p p.k σ s → T p σ s := fun _ _ ⟨_, _, _, _, hs⟩ => hs.t
  have hS := layOk p hp
  have hok : ∀ x ∈ ([(.rsi, .ptr (sc oCT)), (.rdi, .ptr (.r13, 0)), (.rcx, .imm p.ctildeLen)] : List (Reg × Arg)),
      x.2.Ok ∧ x.1 ∈ argRegs := by
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
    have hn' : p.ctildeLen < 2 ^ 31 := by obtain ⟨m, hm, hl⟩ := inB_spec c3; have := (hS _ hm).1; omega
    exact ⟨⟨ptr_ok hS c3, by decide⟩, ⟨ptr_ok hS c4, by decide⟩, ⟨hn', by decide⟩⟩
  refine relInv (fun σ s hv ⟨h, A', q, cH, hs⟩ => WP.mono (tail_ok hp hv hs) fun _ h' => h'.1) ?_
  refine RelCT.seq (RelCT.sameB (RelCT.mono (hash2_tr hS c1) (fun x y h => RV.lrel hp hT h) fun _ _ h => h)
    (fun x y hxy => ?_) (fun x y h => (RV.lrel hp hT h).2.2))
    (cmpAnd_tr hok (by decide) (by decide) fun _ _ h => h)
  have L := RV.lrel hp hT hxy
  exact ⟨WP.mono (hash2_ok L.1 c1) fun _ h' => ⟨_, h'.1⟩, WP.mono (hash2_ok L.2.1 c1) fun _ h' => ⟨_, h'.1⟩⟩

end VG.Proof.MlDsa.X86_64.Verify
