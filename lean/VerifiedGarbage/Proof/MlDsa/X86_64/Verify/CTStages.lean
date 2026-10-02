import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTBase

/-!
# ML-DSA verification on x86-64: constant time, the hint and `z`

Two runs with the same public data (`RV`) run the same code: each piece's
invariant holds of each run from its own inputs (`relInv`), which gives what
each call's trace needs (the pointers, reduced inputs, and the public bytes it
reads); the branches test results that are functions of the signature alone
(the hint is well formed, `z` is small: `ifOk_rel`).
-/

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Proof.MlKem.X86_64
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.Verify (vHint vZ vCt)

theorem layOk : ∀ p ∈ params, LayOk (vB p) := by unfold LayOk; decide

/-- Two runs after a piece `F` from states satisfying `I` keep the layout. -/
theorem RV.lrelStep {p : Params} (hp : p ∈ params) {I : State → State → Prop} (hI : ∀ σ s, I σ s → T p σ s)
    {F : State → State → Prop} (hF : ∀ s₀ s, F s₀ s → ∃ W, PostB s₀ s W) {x y : State}
    (h : RV p (fun σ s => ∃ s₀, I σ s₀ ∧ F s₀ s) x y) : LRel (vR p) (vW p) x y := by
  obtain ⟨σ₁, σ₂, v₁, v₂, pub, ⟨x₀, i₁, f₁⟩, ⟨y₀, i₂, f₂⟩⟩ := h
  obtain ⟨_, hx⟩ := hF _ _ f₁
  obtain ⟨_, hy⟩ := hF _ _ f₂
  exact (RV.lrel hp hI ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩).post hx hy

/-- A piece that keeps the layout leaves two runs with the same pointers. -/
theorem RelCT.sameB {P : State → State → Prop} {c : Prog isa} (ht : RelCT isa P c fun _ _ => True)
    (hw : ∀ x y, P x y → WP isa c x (fun x' => ∃ W, PostB x x' W) ∧ WP isa c y (fun y' => ∃ W, PostB y y' W))
    (hs : ∀ x y, P x y → SameB x y) : RelCT isa P c fun x y => SameB x y :=
  RelCT.postDep ht hw fun x y _ _ hp ⟨_, hx⟩ ⟨_, hy⟩ => (hs x y hp).post hx hy

theorem and15_post (x : State) : WP isa (.block and15) x fun x' => ∃ W, PostB x x' W :=
  WP.mono (and15_ok x) fun x' ⟨⟨_, hm⟩, k⟩ =>
    ⟨_, (postB_of_keep k (by decide) (by rw [hm]; exact Frame.refl _ _) : PPostB x x' [])⟩

theorem sampledTail_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ bases) :
    RelCT isa (fun x y => SameB x y) (.seq (.block and15) (mask a)) fun _ _ => True :=
  RelCT.seq (RelCT.sameB and15_tr (fun x y _ => ⟨and15_post x, and15_post y⟩) fun _ _ h => h)
    (mask_tr hok hb (N := 256) (by decide) fun _ _ h => h)

theorem sampledTail4_tr {a : Ptr} (hok : (Arg.ptr a).Ok) (hb : a.1 ∈ bases) :
    RelCT isa (fun x y => SameB x y) (.seq (.block and15) (mask a 1024)) fun _ _ => True :=
  RelCT.seq (RelCT.sameB and15_tr (fun x y _ => ⟨and15_post x, and15_post y⟩) fun _ _ h => h)
    (mask_tr hok hb (N := 1024) (by decide) fun _ _ h => h)

theorem flag_ne {P : Prop} [Decidable P] (h : (flag P).setWidth 32 ≠ 0) : P := by
  by_contra hn
  exact h (by unfold flag; rw [ifn hn]; rfl)

/-! ## Branches -/

theorem ifOk_rel {p : Params} (hp : p ∈ params) {I It : State → State → Prop} {c : Prog isa}
    (hT : ∀ σ s, I σ s → T p σ s)
    (he : ∀ x y, RV p I x y → (x.gpr .r15).setWidth 32 = (y.gpr .r15).setWidth 32)
    (hk : ∀ σ s₀ s, VPre p σ → I σ s₀ → PPostB s₀ s [] → s.gpr .r15 = s₀.gpr .r15 →
      (s₀.gpr .r15).setWidth 32 ≠ 0 → It σ s)
    (ht : RelCT isa (RV p It) c (RV p (T p))) : RelCT isa (RV p I) (ifOk c) (RV p (T p)) := by
  refine ifOk_tr he (RelCT.mono ht (fun x y ⟨x₀, y₀, ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩, hPx, hPy, ex, ey, hne⟩ =>
    ⟨σ₁, σ₂, v₁, v₂, pub, hk σ₁ x₀ x v₁ i₁ hPx ex hne, hk σ₂ y₀ y v₂ i₂ hPy ey
      (by rw [← he x₀ y₀ ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩]; exact hne)⟩) fun _ _ h => h) ?_
  rintro x y ⟨x₀, y₀, ⟨σ₁, σ₂, v₁, v₂, pub, i₁, i₂⟩, hPx, hPy, _, _, _⟩
  exact ⟨σ₁, σ₂, v₁, v₂, pub, (hT _ _ i₁).step hp v₁ hPx (tChk_nil p hp), (hT _ _ i₂).step hp v₂ hPy (tChk_nil p hp)⟩

/-! ## The hint -/

theorem S1.r15 {p : Params} {σ s : State} (h : S1 p σ s) :
    s.gpr .r15 = flag ((vHint p (vSig p σ)).isSome = true) := by
  unfold S1 at h
  obtain ⟨_, hm⟩ := h
  split at hm
  · rename_i _ hh; rw [hm.1, hh]; exact flag_congr (by simp)
  · rename_i hh; rw [hm, hh]; exact flag_congr (by simp)

theorem hint_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p fun σ s => T p σ s ∧ s.gpr .r15 = flag True) (hint P p) (RV p (S1 p)) := by
  have hc := hintChk_all p hp
  simp only [hintChk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨c1, _⟩, c3⟩, c4⟩ := hc
  refine relInv (fun σ s hv hs => hint_ok C hp hv hs.1) ?_
  unfold hint
  refine RelCT.seq (hintUnpackAt_tr C.hintUnpack (layOk p hp) c3 c1 fun x y h => ?_)
    (block_nomem_tr fun i hi s => by simp only [List.mem_singleton] at hi; subst hi; rfl)
  have L := RV.lrel hp (fun _ _ h => h.1) h
  obtain ⟨σ₁, σ₂, _, _, pub, i₁, i₂⟩ := h
  exact ⟨L.1, L.2.1, L.2.2, by rw [i₁.1.sigSlice c4, i₂.1.sigSlice c4, pub.2.2.2.2.2.2.2]⟩

/-! ## `z` -/

/-- After `z[0], …, z[i - 1]`, with a well-formed hint. -/
def Iz (p : Params) (i : Nat) (σ s : State) : Prop := ∃ h, vHint p (vSig p σ) = some h ∧ S2 p h i σ s

theorem Iz.t {p : Params} {i : Nat} {σ s : State} (h : Iz p i σ s) : T p σ s :=
  let ⟨_, _, hs⟩ := h; hs.t

theorem zOne_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) {i : Nat} (hi : i < p.ℓ) :
    RelCT isa (RV p (Iz p i)) (zOne P p i) (RV p (Iz p (i + 1))) := by
  have hc := zChk_all p hp i hi
  simp only [zChk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, _⟩, _⟩, _⟩, _⟩, c8⟩, c9⟩ := hc
  refine relInv (fun σ s hv ⟨h, hh, hs⟩ => WP.mono (zOne_ok C hp hv hi hs) fun _ h' => ⟨h, hh, h'⟩) ?_
  unfold zOne
  refine RelCT.seq (relInv (I' := fun σ s => ∃ s₀, Iz p i σ s₀ ∧
      (PPostB s₀ s [(pZ i, 1024)] ∧ ∃ f, PolyIs s.mem (pa s₀ (pZ i)) f))
    (fun σ s hv hs => WP.mono (bitUnpackAt_ok C.bitUnpack (hs.t.lay hp hv) c2 c3 c1) fun _ ⟨hP, _, hq⟩ =>
      ⟨s, hs, hP, _, hq⟩)
    (bitUnpackAt_tr C.bitUnpack (layOk p hp) c2 c3 c1 fun x y h => RV.lrel hp (fun _ _ h => h.t) h)) ?_
  refine RelCT.seq (normLtAt_tr C.normLt (layOk p hp) c9 c8 fun x y h => ?_) and15_tr
  have L := RV.lrelStep hp (fun _ _ h => Iz.t h) (fun _ _ f => ⟨_, f.1⟩) h
  obtain ⟨_, _, _, _, _, ⟨x₀, _, fx, _, hx⟩, ⟨y₀, _, fy, _, hy⟩⟩ := h
  exact ⟨L.1, L.2.1, by rw [pa_rbx fx]; exact hx.1, by rw [pa_rbx fy]; exact hy.1, L.2.2⟩

theorem zs_tr {P : Prims} (C : PrimsOk P) {p : Params} (hp : p ∈ params) :
    RelCT isa (RV p (Iz p 0)) (seqR (zOne P p) 0 p.ℓ) (RV p (Iz p p.ℓ)) := by
  have := seqR_tr (R := fun i => RV p (Iz p i)) p.ℓ 0 fun i _ hi => zOne_tr C hp (by omega)
  rwa [Nat.zero_add] at this

end VG.Proof.MlDsa.X86_64.Verify
