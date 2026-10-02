import VerifiedGarbage.Impl.MlDsa.AArch64.Verify.Verify
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Inv
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.MlDsa.Verify.Final
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Norm
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# ML-DSA verification on AArch64: parameters, buffers, and pieces

The facts about the parameter sets the proof uses (`VFacts`); the layout of
the buffers of verification (`pk`, `mu` and `sig` in `x25`, `x26` and `x27`,
read; `scratch` in `x28`, written: `vR p`, `vW p`), which the contract's
precondition gives from the prologue on (`vLay`), and the checks of pointers
into them, which `vlay` proves from the offsets by `omega`; what holds
throughout (`VC`: `Top`, and the inputs); and pieces of code, which take each
run from an invariant to the next and leak the same in two runs whose inputs
agree (`VPiece`), as in key generation.
-/

namespace VG.Proof.MlDsa.AArch64.Verify

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Call VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Proof.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params mlDsa44 mlDsa65 mlDsa87 q gamma2s ballParams simpleBitPackBounds bitlen)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure VFacts (p : Params) : Prop where
  mem : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87
  k : 4 ≤ p.k ∧ p.k ≤ 8
  l : 4 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  pk : p.pkLen = 32 + 320 * p.k
  sig : p.sigLen = p.ctildeLen + lenZ p * p.ℓ + p.ω + p.k
  ct : (p.ctildeLen, p.τ) ∈ ballParams ∧ 32 ≤ p.ctildeLen ∧ p.ctildeLen ≤ 64
  zl : lenZ p * p.ℓ ≤ 640 * 7 ∧ 576 ≤ lenZ p
  bp : BpOk (p.γ₁ - 1) p.γ₁ (lenZ p)
  g1 : p.γ₁ ∈ Proof.MlDsa.Verify.gamma1s ∧ 0 < p.γ₁ - p.β ∧ p.γ₁ - p.β < 2 ^ 32
  hu : HuOk (p.ω + p.k) p.ω (256 * p.k)
  om : p.ω ≤ 80
  sbp : SbpOk (w1Max p) (w1Len p)
  w1 : p.k * w1Len p ≤ 1024
  g2 : p.γ₂ ∈ gamma2s ∧ w1Max p = (q - 1) / (2 * p.γ₂) - 1
  wl : w1Len p = 192 ∨ w1Len p = 128

theorem vfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : VFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by simp, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      ⟨by decide, by decide, by decide⟩, by decide, ⟨by decide, by decide, by decide, by decide⟩, by decide,
      ⟨by decide, by decide, by decide⟩, by decide, by decide, by decide⟩

theorem VFacts.small {p : Params} (hF : VFacts p) : scrLen p < 2 ^ 32 ∧ p.pkLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl; have := hF.zl; have := hF.ct; have := hF.om
  exact ⟨by rw [scr_eq]; omega, by rw [hF.pk]; omega, by rw [hF.sig]; omega⟩

/-! ## The contract -/

/-- The precondition of the shared contract. -/
abbrev vPre (p : Params) (S : Nat) (σ : State) : Prop := (Spec.MlDsa.verifyContract p AArch64.abi S).pre σ
/-- Its public data. -/
abbrev vPub (p : Params) (S : Nat) (σ₁ σ₂ : State) : Prop := (Spec.MlDsa.verifyContract p AArch64.abi S).pub σ₁ σ₂

/-- The inputs of a run from `σ`. -/
abbrev vPk (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0) p.pkLen
abbrev vMu (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x1) 64
abbrev vSig (p : Params) (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x2) p.sigLen

theorem vPub_eq {p : Params} {S : Nat} {σ₁ σ₂ : State} (h : vPub p S σ₁ σ₂) :
    σ₁.sp = σ₂.sp ∧ vPk p σ₁ = vPk p σ₂ ∧ vMu σ₁ = vMu σ₂ ∧ vSig p σ₁ = vSig p σ₂ ∧
      σ₁.gpr .x0 = σ₂.gpr .x0 ∧ σ₁.gpr .x1 = σ₂.gpr .x1 ∧ σ₁.gpr .x2 = σ₂.gpr .x2 ∧ σ₁.gpr .x3 = σ₂.gpr .x3 := by
  unfold vPub at h
  sig_pub [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at h
  obtain ⟨hsp, hb, e0, e1, e2, e3⟩ := h
  have hb' := Proof.MlDsa.KeyGen.leakBytes_inj hb
  have l1 : (vPk p σ₁ ++ vMu σ₁).length = (vPk p σ₂ ++ vMu σ₂).length := by
    simp only [List.length_append, Proof.MlKem.bytesAt_length]
  obtain ⟨h12, h3⟩ := List.append_inj hb' l1
  obtain ⟨h1, h2⟩ := List.append_inj h12 (by simp only [Proof.MlKem.bytesAt_length])
  exact ⟨hsp, h1, h2, h3, e0, e1, e2, e3⟩

/-! ## The layout -/

/-- `pk`, `mu` and `sig`. -/
abbrev vR (p : Params) : List (Reg × Nat) := [(.x25, p.pkLen), (.x26, 64), (.x27, p.sigLen)]
/-- `scratch`. -/
abbrev vW (p : Params) : List (Reg × Nat) := [(.x28, scrLen p)]

theorem vLay {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ) (h : Top σ s) :
    Lay S (vR p) (vW p) s := by
  unfold vPre at hp
  sig_pre [Spec.MlDsa.verifyContract, Spec.MlDsa.verifySig, AArch64.abi, VG.AArch64.argRegs] at hp
  obtain ⟨hwf, hrd, hwr, d03, d13, d23, hres, n0, n1, n2, n3⟩ := hp
  obtain ⟨k0, k1, k2, k3⟩ := below_of_resv hres
  have hS : S ≤ σ.sp.toNat := le_of_wfP hwf
  have hsm := hF.small
  have e25 := h.x25; have e26 := h.x26; have e27 := h.x27; have e28 := h.x28
  have mrd : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr => by
    rw [h.rd, h.wr]; exact inR_self hr
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [h.sp]; exact hS⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl)
    exacts [hsm.2.1, by decide, hsm.2.2, hsm.1]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    have w : ∀ r, isW (vW p) r = (r == .x28) := fun r => by cases r <;> rfl
    rintro b (rfl | rfl | rfl | rfl) b' (rfl | rfl | rfl | rfl) hne hw <;>
      simp only [w, e25, e26, e27, e28] at hne hw ⊢ <;> revert hne hw
    all_goals first
      | exact fun h => absurd rfl h
      | exact fun _ h => absurd h (by decide)
      | exact fun _ _ => d03 | exact fun _ _ => d13 | exact fun _ _ => d23 | exact fun _ _ => d03.symm
      | exact fun _ _ => d13.symm | exact fun _ _ => d23.symm
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28, h.sp]
    exacts [k0, k1, k2, k3]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28]
    exacts [n0, n1, n2, n3]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28]
    · exact mrd ⟨σ.gpr .x0, p.pkLen⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x1, 64⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x2, p.sigLen⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x3, scrLen p⟩ (by rw [hwr]; simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro b rfl
    simp only [e28, h.wr]
    exact inR_self (r := ⟨σ.gpr .x3, scrLen p⟩) (by rw [hwr]; simp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp

theorem vOk (p : Params) : LayOk (vR p ++ vW p) := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp

/-! ## Checks of pointers, by `omega` -/

theorem vinB_x25 (p : Params) (o l : Nat) :
    inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: vW p) (.x25, o) l = decide (o + l ≤ p.pkLen) :=
  rfl
theorem vinB_x26 (p : Params) (o l : Nat) :
    inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: vW p) (.x26, o) l = decide (o + l ≤ 64) :=
  rfl
theorem vinB_x27 (p : Params) (o l : Nat) :
    inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: vW p) (.x27, o) l = decide (o + l ≤ p.sigLen) :=
  rfl
theorem vinB_x28 (p : Params) (o l : Nat) :
    inB ((Reg.x25, p.pkLen) :: (Reg.x26, 64) :: (Reg.x27, p.sigLen) :: vW p) (.x28, o) l = decide (o + l ≤ scrLen p) :=
  rfl
theorem vinB_x28W (p : Params) (o l : Nat) : inB (vW p) (.x28, o) l = decide (o + l ≤ scrLen p) := rfl

theorem sepB_v {p : Params} {r r' : Reg} (h : r ≠ r') (hw : r = .x28 ∨ r' = .x28) (o l o' l' : Nat) :
    sepB (vR p) (vW p) (r, o) l (r', o') l' =
      (inB (vR p ++ vW p) (r, o) l && inB (vR p ++ vW p) (r', o') l') := by
  refine sepB_ne h ?_ o l o' l'
  rcases hw with rfl | rfl <;> simp [isW, List.lookup]

/-- Unfolds the checks of pointers into the layout into arithmetic, then `omega`. -/
syntax "vlay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| vlay) => `(tactic| vlay [])
  | `(tactic| vlay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlDsa.AArch64.keepB,
        VG.Proof.MlDsa.AArch64.sepB_same, VG.Proof.MlDsa.AArch64.Verify.sepB_v,
        VG.Proof.MlDsa.AArch64.Verify.vinB_x25, VG.Proof.MlDsa.AArch64.Verify.vinB_x26,
        VG.Proof.MlDsa.AArch64.Verify.vinB_x27, VG.Proof.MlDsa.AArch64.Verify.vinB_x28,
        VG.Proof.MlDsa.AArch64.Verify.vinB_x28W, List.all_cons, List.all_nil, List.cons_append, List.nil_append,
        List.all_append, Bool.and_self,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, true_and, and_true,
        ↓reduceIte, Bool.false_eq_true, $ls,*]
      set_option linter.unusedSimpArgs false in
      try simp only [VG.Impl.MlDsa.AArch64.KeyGen.oP, VG.Impl.MlDsa.AArch64.KeyGen.oSA,
        VG.Impl.MlDsa.AArch64.KeyGen.oSS, VG.Impl.MlDsa.AArch64.KeyGen.SV, VG.Impl.MlDsa.AArch64.Verify.oCT,
        VG.Impl.MlDsa.AArch64.Verify.oHint, or_true, true_or, and_true, true_and, $ls,*]
      and_intros <;> omega_arith))

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`: `Top`, and the inputs. -/
structure VC (p : Params) (σ s : State) : Prop where
  top : Top σ s
  pk : bytesAt s.mem (pa s (.x25, 0)) p.pkLen = vPk p σ
  mu : bytesAt s.mem (pa s (.x26, 0)) 64 = vMu σ
  sig : bytesAt s.mem (pa s (.x27, 0)) p.sigLen = vSig p σ

/-- A piece that writes `ws` keeps `VC`. -/
def vcChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  keepB (vR p) (vW p) ws svP 48 && keepB (vR p) (vW p) ws (.x25, 0) p.pkLen &&
    keepB (vR p) (vW p) ws (.x26, 0) 64 && keepB (vR p) (vW p) ws (.x27, 0) p.sigLen

section
variable {p : Params} (hF : VFacts p) {S : Nat} {σ : State} (hp : vPre p S σ)
include hF hp

theorem VC.lay {s : State} (h : VC p σ s) : Lay S (vR p) (vW p) s := vLay hF hp h.top

theorem VC.step {s s' : State} (h : VC p σ s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws)
    (hc : vcChk p ws = true) : VC p σ s' := by
  simp only [vcChk, Bool.and_eq_true] at hc
  have L := h.lay hF hp
  exact ⟨h.top.step L hP hc.1.1.1, by rw [L.keepBytes hP hc.1.1.2]; exact h.pk,
    by rw [L.keepBytes hP hc.1.2]; exact h.mu, by rw [L.keepBytes hP hc.2]; exact h.sig⟩

end

/-! ## Two runs -/

/-- Two runs in the layout, with the same pointers and stack pointer. -/
structure VTwo (p : Params) (S : Nat) (x y : State) : Prop where
  lx : Lay S (vR p) (vW p) x
  ly : Lay S (vR p) (vW p) y
  same : SameB x y

theorem vc_two {p : Params} (hF : VFacts p) {S : Nat} {σ₁ σ₂ x y : State} (p₁ : vPre p S σ₁) (p₂ : vPre p S σ₂)
    (pub : vPub p S σ₁ σ₂) (h₁ : VC p σ₁ x) (h₂ : VC p σ₂ y) : VTwo p S x y := by
  obtain ⟨esp, _, _, _, e0, e1, e2, e3⟩ := vPub_eq pub
  refine ⟨h₁.lay hF p₁, h₂.lay hF p₂, fun r hr => ?_, by rw [h₁.top.sp, h₂.top.sp, esp]⟩
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.top.x25, h₂.top.x25, e0]
  · rw [h₁.top.x26, h₂.top.x26, e1]
  · rw [h₁.top.x27, h₂.top.x27, e2]
  · rw [h₁.top.x28, h₂.top.x28, e3]

theorem VTwo.x28 {p : Params} {S : Nat} {x y : State} (h : VTwo p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ [Reg.x28], x.gpr r = y.gpr r := ⟨h.same.2, fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.same.1 .x28 (by decide)⟩

theorem VTwo.bases {p : Params} {S : Nat} {x y : State} (h : VTwo p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r := ⟨h.same.2, h.same.1⟩

/-! ## Pieces -/

abbrev VR (p : Params) (S : Nat) (I : State → State → Prop) : State → State → Prop :=
  Rel2 (vPre p S) (vPub p S) I

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure VPiece (p : Params) (S : Nat) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, vPre p S σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (VR p S I) c fun _ _ => True

section
variable {p : Params} {S : Nat} {I J K : State → State → Prop}

theorem VPiece.seq {c₁ c₂ : Prog isa} (h₁ : VPiece p S I J c₁) (h₂ : VPiece p S J K c₂) :
    VPiece p S I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem VPiece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : VPiece p S I J c)
    (hI : ∀ σ s, vPre p S σ → I' σ s → I σ s) (hJ : ∀ σ s, vPre p S σ → J σ s → J' σ s) :
    VPiece p S I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem VPiece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → VPiece p S (I k) (I (k + 1)) (f k)) →
      VPiece p S (I a) (I (a + n)) (seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (Q := fun k => VR p S (I k)) n a fun k h₁ h₂ => relInv (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem vrel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, vPre p S σ₁ → vPre p S σ₂ → vPub p S σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (VR p S I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

/-- A branch, both ways: the condition agrees in both runs. -/
theorem relIte {P Q : State → State → Prop} {c : Cond} {th el : Prog isa}
    (hc : ∀ s₁ s₂, P s₁ s₂ → isa.eval c s₁ = isa.eval c s₂)
    (ht : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some true) th Q)
    (he : RelCT isa (fun s₁ s₂ => P s₁ s₂ ∧ isa.eval c s₁ = some false) el Q) :
    RelCT isa P (.ite c th el) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hce := hc _ _ hp
  cases e₁ with
  | iteT c₁ b₁ =>
    cases e₂ with
    | iteT _ b₂ =>
      obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ ⟨hp, c₁⟩ b₁ b₂
      exact ⟨rfl, hq⟩
    | iteF c₂ _ => rw [c₁, c₂] at hce; cases hce
  | iteF c₁ b₁ =>
    cases e₂ with
    | iteT c₂ _ => rw [c₁, c₂] at hce; cases hce
    | iteF _ b₂ =>
      obtain ⟨rfl, hq⟩ := he _ _ _ _ _ _ ⟨hp, c₁⟩ b₁ b₂
      exact ⟨rfl, hq⟩

theorem eval24 (s : State) : isa.eval (.nonzero .x .x24) s = some (s.gpr .x24 != 0) := rfl

/-- `c` if `x24 ≠ 0`, where `x24` is whether `T σ` holds, which depends on public data only. -/
theorem VPiece.ifOk {c : Prog isa} {T : State → Prop} [DecidablePred T]
    (hx : ∀ σ s, vPre p S σ → I σ s → s.gpr .x24 = if T σ then 1 else 0)
    (hT : ∀ σ₁ σ₂, vPre p S σ₁ → vPre p S σ₂ → vPub p S σ₁ σ₂ → (T σ₁ ↔ T σ₂))
    (ht : VPiece p S (fun σ s => I σ s ∧ T σ) J c) (he : ∀ σ s, vPre p S σ → I σ s → ¬ T σ → J σ s) :
    VPiece p S I J (ifOk c) := by
  have ev : ∀ σ s, vPre p S σ → I σ s → isa.eval (.nonzero .x .x24) s = some (decide (T σ)) := fun σ s hp hs => by
    rw [eval24, hx σ s hp hs]; by_cases h : T σ <;> simp [h]
  refine ⟨fun σ s hp hs => WP.ite (decide (T σ)) (ev σ s hp hs) (fun hb => ht.ok σ s hp ⟨hs, of_decide_eq_true hb⟩)
    fun hb => WP.block_nil (he σ s hp hs (of_decide_eq_false hb)), relIte ?_ ?_ ?_⟩
  · rintro x y ⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩
    rw [ev σ₁ x p₁ h₁, ev σ₂ y p₂ h₂, decide_eq_decide.mpr (hT σ₁ σ₂ p₁ p₂ pub)]
  · refine RelCT.mono ht.tr (fun x y ⟨⟨σ₁, σ₂, p₁, p₂, pub, h₁, h₂⟩, hc⟩ => ?_) fun _ _ h => h
    rw [ev σ₁ x p₁ h₁] at hc
    have t₁ : T σ₁ := of_decide_eq_true (Option.some.inj hc)
    exact ⟨σ₁, σ₂, p₁, p₂, pub, ⟨h₁, t₁⟩, h₂, (hT σ₁ σ₂ p₁ p₂ pub).mp t₁⟩
  · exact RelCT.block_nil fun _ _ _ => trivial

end

end VG.Proof.MlDsa.AArch64.Verify
