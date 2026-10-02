import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PhaseL

/-!
# ML-DSA signing on AArch64: the loop leaks what `signLeakT` says

Two runs whose remaining iterations leak the same (`LeakEq`) agree on the
iteration's `c̃` (`leq_ct`), on whether it passes (`leq_pass`) and on its hint
if it does (`leq_hints`), and, if it is rejected, on what the rest leaks
(`leq_succ`); so they agree on the branches of each iteration, and leak the
same (`iter_tr`, `signLoop_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

variable {keccak : VG.Proof.Sha3.AArch64.Permutation}

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc Arg glue callAt setB and24 seqR movV lea)
open VG.Proof.MlKem.AArch64 (Only Keep)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## What the iterations leak -/

section
variable (p : Params)

/-- What the `n` iterations from counter `κ` leak, for the function entered in `σ`. -/
abbrev leakL (σ : State) (n κ : Nat) : List Nat :=
  signLeakLoopT p maxBounds (amat p (Am p σ)) ((List.range p.ℓ).map (S1v p σ)) ((List.range p.k).map (S2v p σ))
    ((List.range p.k).map (T0v p σ)) (muOf σ) (rppOf p σ) n κ

/-- Two runs agree on what the iterations from `t` leak. -/
abbrev LeakEq (t : Nat) (σ₁ σ₂ : State) : Prop := leakL p σ₁ (1000 - t) (p.ℓ * t) = leakL p σ₂ (1000 - t) (p.ℓ * t)

end

theorem map_toNat_inj : ∀ {l₁ l₂ : List Bool}, l₁.map Bool.toNat = l₂.map Bool.toNat → l₁ = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [map_toNat_inj h.2]
    cases a <;> cases b <;> simp_all
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem hints_inj : ∀ {a b : List (Vector Bool n)}, a.length = b.length →
    (a.flatMap fun hi => hi.toList.map Bool.toNat) = (b.flatMap fun hi => hi.toList.map Bool.toNat) → a = b
  | [], [], _, _ => rfl
  | x :: a, y :: b, hl, h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    rw [Vector.toList_inj.mp (map_toNat_inj h1), hints_inj (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

section
variable {p : Params} {σ₁ σ₂ : State} {t : Nat}

theorem leq_step (h : LeakEq p t σ₁ σ₂) (ht : t < 814) :
    signLeakLoopT p maxBounds (amat p (Am p σ₁)) ((List.range p.ℓ).map (S1v p σ₁)) ((List.range p.k).map (S2v p σ₁))
      ((List.range p.k).map (T0v p σ₁)) (muOf σ₁) (rppOf p σ₁) ((999 - t) + 1) (p.ℓ * t) =
    signLeakLoopT p maxBounds (amat p (Am p σ₂)) ((List.range p.ℓ).map (S1v p σ₂)) ((List.range p.k).map (S2v p σ₂))
      ((List.range p.k).map (T0v p σ₂)) (muOf σ₂) (rppOf p σ₂) ((999 - t) + 1) (p.ℓ * t) := by
  rw [show 999 - t + 1 = 1000 - t by omega]; exact h

theorem leq_ct (h : LeakEq p t σ₁ σ₂) (ht : t < 814) : CTv p σ₁ (p.ℓ * t) = CTv p σ₂ (p.ℓ * t) := by
  have := (leakT_step (leq_step h ht)).1
  rwa [signCommit_eq, signCommit_eq] at this

theorem leq_succ (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hr : ∃ ct, iterF p σ₁ maxBounds (p.ℓ * t) = some (ct, none)) : LeakEq p (t + 1) σ₁ σ₂ := by
  have := ((leakT_step (leq_step h ht)).2.1 hr).2
  unfold LeakEq
  rw [show 1000 - (t + 1) = 999 - t by omega, Nat.mul_succ]
  exact this

theorem outTag_eq (hp : ParamsOk p) {σ : State} {κ : Nat} (hs : (sampleInBall p.τ maxBounds.ball (CTv p σ κ)).isSome) :
    outTag (iterF p σ maxBounds κ) = if PassV p σ κ then
      1 :: ((List.range p.k).map (Hv p σ κ)).flatMap (fun hi => hi.toList.map Bool.toNat) else [0] := by
  rw [iterF_eq hp, cV_eq hs, Option.map_some]
  by_cases hv : PassV p σ κ
  · rw [ifp hv, ifp hv]; rfl
  · rw [ifn hv, ifn hv]; rfl

theorem leq_pass (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome) :
    PassV p σ₁ (p.ℓ * t) ↔ PassV p σ₂ (p.ℓ * t) := by
  have e := (leakT_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂] at e
  by_cases h1 : PassV p σ₁ (p.ℓ * t) <;> by_cases h2 : PassV p σ₂ (p.ℓ * t)
  · exact iff_of_true h1 h2
  · rw [ifp h1, ifn h2] at e; cases e
  · rw [ifn h1, ifp h2] at e; cases e
  · exact iff_of_false h1 h2

theorem leq_hints (hp : ParamsOk p) (h : LeakEq p t σ₁ σ₂) (ht : t < 814)
    (hs₁ : (sampleInBall p.τ maxBounds.ball (CTv p σ₁ (p.ℓ * t))).isSome)
    (hs₂ : (sampleInBall p.τ maxBounds.ball (CTv p σ₂ (p.ℓ * t))).isSome)
    (h1 : PassV p σ₁ (p.ℓ * t)) (h2 : PassV p σ₂ (p.ℓ * t)) :
    (List.range p.k).map (Hv p σ₁ (p.ℓ * t)) = (List.range p.k).map (Hv p σ₂ (p.ℓ * t)) := by
  have e := (leakT_step (leq_step h ht)).2.2
  rw [outTag_eq hp hs₁, outTag_eq hp hs₂, ifp h1, ifp h2] at e
  exact hints_inj (by simp) (List.cons.inj e).2

end

/-! ## Pieces from runs related through their entry states -/

section
variable {p : Params} {D : Nat}

/-- A piece that takes each run from `I` to `J` (and `s` to `s'` with `F s s'`), and leaks the same from runs
related by `RS p D E I` and `G`, with `Q₀` of the final states. -/
theorem liftQ {E I J G Q₀ Q F : State → State → Prop} {c : Prog isa}
    (hw : ∀ σ s, (signK p D).pre σ → I σ s → WP isa c s fun s' => J σ s' ∧ F s s')
    (ht : RelCT isa (fun x y => RS p D E I x y ∧ G x y) c Q₀)
    (hQ : ∀ σ₁ σ₂ x y x' y', (signK p D).pre σ₁ → (signK p D).pre σ₂ → (signK p D).pub σ₁ σ₂ → E σ₁ σ₂ →
      I σ₁ x → I σ₂ y → G x y → J σ₁ x' → J σ₂ y' → F x x' → F y y' → Q₀ x' y' → Q x' y') :
    RelCT isa (fun x y => RS p D E I x y ∧ G x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  obtain ⟨ht', hq⟩ := ht _ _ _ _ _ _ hr e₁ e₂
  obtain ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩ := hr
  obtain ⟨_, u₁, f₁, j₁, g₁⟩ := hw σ₁ s₁ p₁ i₁
  obtain ⟨_, u₂, f₂, j₂, g₂⟩ := hw σ₂ s₂ p₂ i₂
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht', hQ _ _ _ _ _ _ p₁ p₂ hpub he i₁ i₂ hg j₁ j₂ g₁ g₂ hq⟩

theorem relOr {P₁ P₂ Q : State → State → Prop} {c : Prog isa} (h₁ : RelCT isa P₁ c Q) (h₂ : RelCT isa P₂ c Q) :
    RelCT isa (fun x y => P₁ x y ∨ P₂ x y) c Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hr e₁ e₂
  rcases hr with h | h
  exacts [h₁ _ _ _ _ _ _ h e₁ e₂, h₂ _ _ _ _ _ _ h e₁ e₂]

end

theorem LP.il {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : LP p D σ t s) (hz : s.gpr .x9 ≠ 0) :
    IL p D σ (t + 1) s := by
  rcases h with ⟨_, h⟩ | ⟨h, _⟩
  · exact h
  · exact absurd h hz

theorem LP.xs {p : Params} {D : Nat} {σ : State} {t : Nat} {s : State} (h : LP p D σ t s) (hz : s.gpr .x9 = 0) :
    XS p D σ s := by
  rcases h with ⟨h, _⟩ | ⟨_, h⟩
  · exact absurd hz h
  · exact h

theorem x9_ne {s : State} (h : isa.eval (.nonzero .x .x9) s = some true) : s.gpr .x9 ≠ 0 := by
  rw [eval_x9] at h; simpa using h

theorem x9_zero {s : State} (h : isa.eval (.nonzero .x .x9) s = some false) : s.gpr .x9 = 0 := by
  rw [eval_x9] at h; simpa using h

/-! ## An iteration -/

/-- The loop ended in both runs: they agree on whether it succeeded, and if it did, on `c̃` and `h`. -/
abbrev OX (p : Params) (D : Nat) (x y : State) : Prop :=
  RS p D (fun _ _ => True) (XS p D) x y ∧ x.gpr .x24 = y.gpr .x24 ∧
    (x.gpr .x24 = 1 → bytesAt x.mem (pa x (sc oCT)) (cLen p) = bytesAt y.mem (pa y (sc oCT)) (cLen p) ∧
      ∃ f, HFam x 5 p.k f ∧ HFam y 5 p.k f)

/-- After iteration `t` of two runs: both continue, leaking the same from then on, or both end. -/
abbrev IX (p : Params) (D : Nat) (t : Nat) (x y : State) : Prop :=
  x.gpr .x9 = y.gpr .x9 ∧ (x.gpr .x9 ≠ 0 → RS p D (LeakEq p (t + 1)) (fun σ s => IL p D σ (t + 1) s) x y) ∧
    (x.gpr .x9 = 0 → OX p D x y)

section
variable {p : Params} {D : Nat}

theorem endPF_tr (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RS p D (LeakEq p t) (fun σ s => EP p D σ t s ∨ EF p D σ t s) x y ∧ True)
      (.block cntDec) (IX p D t) := by
  refine liftQ (J := fun σ s => LP p D σ t s) (fun σ s _ h => WP.conj (dec_end hp hc (h.elim .inl (.inr ∘ .inl)))
      (decF hc (h.elim (·.k) (·.k))))
    (lrel_tr (fun x y h => h.1.lrel fun σ s h => h.elim (·.k.d.im.st) (·.k.d.im.st)) (by taint_decide)) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub he i₁ i₂ _ j₁ j₂ ⟨z₁, r₁, b₁, h₁⟩ ⟨z₂, r₂, b₂, h₂⟩ _
  rcases i₁ with e₁ | f₁ <;> rcases i₂ with e₂ | f₂
  · have zx : x'.gpr .x9 = 0 := by rw [z₁, e₁.cnt, one_sub_one]
    have zy : y'.gpr .x9 = 0 := by rw [z₂, e₂.cnt, one_sub_one]
    refine ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
      j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.x24, e₂.x24], fun _ => ⟨by rw [b₁, b₂, e₁.ct, e₂.ct]; exact leq_ct he e₁.t_lt,
      Hv p σ₁ (p.ℓ * t), h₁ _ e₁.h, h₂ _ fun j hj => ?_⟩⟩⟩
    rw [List.map_inj_left.mp (leq_hints hp he e₁.t_lt e₁.some e₂.some e₁.pass e₂.pass) j (List.mem_range.mpr hj)]
    exact e₂.h j hj
  · exact absurd ((leq_pass hp he e₁.t_lt e₁.some f₂.some).mp e₁.pass) f₂.fail
  · exact absurd ((leq_pass hp he f₁.t_lt f₁.some e₂.some).mpr e₂.pass) f₁.fail
  · have zxy : x'.gpr .x9 = y'.gpr .x9 := by rw [z₁, z₂, f₁.cnt, f₂.cnt]
    refine ⟨zxy, fun h => ⟨σ₁, σ₂, p₁, p₂, hpub, leq_succ he f₁.t_lt ⟨_, iter_rej hp f₁.some f₁.fail⟩,
      j₁.il h, j₂.il (zxy ▸ h)⟩, fun h => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial, j₁.xs h, j₂.xs (zxy ▸ h)⟩,
      by rw [r₁, r₂, f₁.x24, f₂.x24], fun h1 => absurd (h1.symm.trans (r₁.trans f₁.x24)) (by decide)⟩⟩

theorem endB_tr (hp : ParamsOk p) (hc : lChk p = true) {t : Nat} :
    RelCT isa (fun x y => RS p D (LeakEq p t) (fun σ s => EB p D σ t s) x y ∧ True) (.block cntDec) (IX p D t) := by
  refine liftQ (J := fun σ s => LP p D σ t s) (fun σ s _ h => WP.conj (dec_end hp hc (.inr (.inr h))) (decF hc h.k))
    (lrel_tr (fun x y h => h.1.lrel fun σ s h => h.k.d.im.st) (by taint_decide)) ?_
  intro σ₁ σ₂ x y x' y' p₁ p₂ hpub _ e₁ e₂ _ j₁ j₂ ⟨z₁, r₁, _⟩ ⟨z₂, r₂, _⟩ _
  have zx : x'.gpr .x9 = 0 := by rw [z₁, e₁.cnt, one_sub_one]
  have zy : y'.gpr .x9 = 0 := by rw [z₂, e₂.cnt, one_sub_one]
  exact ⟨by rw [zx, zy], fun h => absurd zx h, fun _ => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, trivial,
    j₁.xs zx, j₂.xs zy⟩, by rw [r₁, r₂, e₁.x24, e₂.x24],
    fun h1 => absurd (h1.symm.trans (r₁.trans e₁.x24)) (by decide)⟩⟩

theorem x0_one {s : State} (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1)
    (hb : isa.eval (.nonzero .w .x0) s = some true) : (s.gpr .x0).setWidth 32 = 1 := by
  rw [eval_w0] at hb
  rcases hr with h | h
  · rw [h] at hb; cases hb
  · exact h

theorem x0_zero {s : State} (hb : isa.eval (.nonzero .w .x0) s = some false) : (s.gpr .x0).setWidth 32 = 0 := by
  rw [eval_w0] at hb; simpa using hb

theorem iter_tr {P : Prims} (hP : PrimsOk P D) (h3 : Ok3 p) (hc1 : cChk p = true) (hc2 : bChk p = true)
    (hc3 : ksChk p = true) (hc4 : lChk p = true) {t : Nat} (ht : t < 814) :
    RelCT isa (RS p D (LeakEq p t) fun σ s => IL p D σ t s) (iterWith keccak.callee P p) (IX p D t) := by
  have hp := paramsOk h3
  have hc2' := hc2
  simp only [bChk, Bool.and_eq_true, decide_eq_true_eq] at hc2'
  obtain ⟨⟨⟨c1, -⟩, -⟩, hbp⟩ := hc2'
  unfold iterWith
  refine RelCT.seq (commit_tr hP h3 hc1) ?_
  refine RelCT.seq (R := fun x y => RS p D (LeakEq p t) (fun σ s => IB p D σ t s) x y ∧
      (x.gpr .x0).setWidth 32 = (y.gpr .x0).setWidth 32)
    (RelCT.mono (liftQ (G := fun _ _ => True) (J := fun σ s => IB p D σ t s) (F := fun _ _ => True)
      (fun _ _ _ h => WP.mono (ball_ok hP hc2 h) fun _ h => ⟨h, trivial⟩)
      (RelCT.mono (ballCall_tr hP hbp c1) (fun x y ⟨h, _⟩ => ⟨h.lrel (fun _ _ h => h.c.l.st), by
        obtain ⟨σ₁, σ₂, _, _, _, he, i₁, i₂⟩ := h
        rw [i₁.ct, i₂.ct]; exact leq_ct he ht⟩) fun _ _ h => h)
      fun σ₁ σ₂ x y x' y' p₁ p₂ hpub he _ _ _ j₁ j₂ _ _ hq => ⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, j₁, j₂⟩, hq⟩)
      (fun x y h => ⟨h, trivial⟩) fun _ _ h => h) ?_
  refine RelCT.seq (R := fun x y => (RS p D (LeakEq p t) (fun σ s => EP p D σ t s ∨ EF p D σ t s) x y ∧ True) ∨
      (RS p D (LeakEq p t) (fun σ s => EB p D σ t s) x y ∧ True)) (RelCT.ite ?_ ?_ ?_)
    (relOr (endPF_tr hp hc4) (endB_tr hp hc4))
  · rintro x y ⟨_, hg⟩
    rw [eval_w0, eval_w0, hg]
  · refine RelCT.mono (checks_tr hP hc3 fun σ₁ σ₂ he s₁ s₂ => leq_pass hp he ht s₁ s₂)
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inl ⟨h, trivial⟩
    have h1 := x0_one i₁.r01 hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁.ka h1, i₂.ka (hg.symm.trans h1)⟩
  · refine RelCT.mono (liftT (I := fun σ s => IB p D σ t s ∧ (s.gpr .x0).setWidth 32 = 0)
      (J := fun σ s => EB p D σ t s) (fun _ _ h => h.1.c.l.st) (fun _ _ _ h => else_ok hc4 h.1 h.2)
      (lrel_tr (fun x y h => h) (by taint_decide)))
      (fun x y ⟨⟨⟨σ₁, σ₂, p₁, p₂, hpub, he, i₁, i₂⟩, hg⟩, hb⟩ => ?_) fun _ _ h => .inr ⟨h, trivial⟩
    have h0 := x0_zero hb
    exact ⟨σ₁, σ₂, p₁, p₂, hpub, he, ⟨i₁, h0⟩, ⟨i₂, hg.symm.trans h0⟩⟩

/-! ## The loop -/

theorem signLoop_tr {P : Prims} (hP : PrimsOk P D) (h3 : Ok3 p) (hc1 : cChk p = true) (hc2 : bChk p = true)
    (hc3 : ksChk p = true) (hc4 : lChk p = true) :
    RelCT isa (RS p D (LeakEq p 0) fun σ s => IK p D σ s) (Impl.MlDsa.AArch64.Sign.signLoopWith keccak.callee P p) (OX p D) := by
  unfold Impl.MlDsa.AArch64.Sign.signLoopWith
  refine RelCT.seq (liftT (J := fun σ s => IL p D σ 0 s) (fun _ _ h => h.d.im.st) (fun _ _ _ h => loopInit_ok hc4 h)
    (lrel_tr (fun x y h => h) (by taint_decide))) ?_
  refine RelCT.mono (RelCT.loop (M := isa)
    (fun n x y => ∃ t, n = 814 - t ∧ RS p D (LeakEq p t) (fun σ s => IL p D σ t s) x y) (fun n => ?_) 814)
    (fun x y h => ⟨0, rfl, h⟩) fun _ _ h => h
  intro s₁ s₂ t₁ t₂ s₁' s₂' ⟨t, hn, hr⟩ e₁ e₂
  have ht : t < 814 := by obtain ⟨_, _, _, _, _, _, i₁, _⟩ := hr; exact i₁.t_lt
  obtain ⟨htr, hz, hc, ho⟩ := iter_tr hP h3 hc1 hc2 hc3 hc4 ht _ _ _ _ _ _ hr e₁ e₂
  refine ⟨htr, by rw [eval_x9, eval_x9, hz], fun h => ho (x9_zero h), fun h =>
    ⟨814 - (t + 1), by omega, t + 1, rfl, hc (x9_ne h)⟩⟩

end

end VG.Proof.MlDsa.AArch64.Sign
