import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Lay
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-!
# ML-DSA key generation on AArch64: what holds throughout, and pieces

What holds of the state throughout (`KC`: `Top`, and the seed `ξ` at `seed`),
two runs in the layout (`Two`), and a piece of code (`Piece p S I J c`): it
takes each run from `I` to `J` (`ok`), and two runs related by `I` leak the
same (`tr`). Pieces compose (`Piece.seq`, `Piece.seqR`), which proves
correctness and constant time together.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds)
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The precondition of the shared contract. -/
abbrev kgPre (p : Params) (S : Nat) (σ : State) : Prop := (Spec.MlDsa.keyGenContract p AArch64.abi S).pre σ
/-- Its public data. -/
abbrev kgPub (p : Params) (S : Nat) (σ₁ σ₂ : State) : Prop := (Spec.MlDsa.keyGenContract p AArch64.abi S).pub σ₁ σ₂

theorem kgPub_eq {p : Params} {S : Nat} {σ₁ σ₂ : State} (h : kgPub p S σ₁ σ₂) :
    σ₁.sp = σ₂.sp ∧ Spec.MlDsa.keyGenLeak p (bytesAt σ₁.mem (σ₁.gpr .x0) 32) =
        Spec.MlDsa.keyGenLeak p (bytesAt σ₂.mem (σ₂.gpr .x0) 32) ∧
      σ₁.gpr .x0 = σ₂.gpr .x0 ∧ σ₁.gpr .x1 = σ₂.gpr .x1 ∧ σ₁.gpr .x2 = σ₂.gpr .x2 ∧ σ₁.gpr .x3 = σ₂.gpr .x3 := by
  unfold kgPub at h
  sig_pub [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at h
  exact h

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .x0) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.2

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  top : Top σ s
  xi : bytesAt s.mem (pa s (.x25, 0)) 32 = xiOf σ

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (p : Params) (ws : List (Ptr × Nat)) : Bool :=
  keepB kgR (kgW p) ws svP 48 && keepB kgR (kgW p) ws (.x25, 0) 32

section
variable {p : Params} (hF : PFacts p) {S : Nat} {σ : State} (hp : kgPre p S σ)
include hF hp

theorem KC.lay {s : State} (h : KC p σ s) : Lay S kgR (kgW p) s := kgLay hF hp h.top

theorem KC.step {s s' : State} (h : KC p σ s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws)
    (hc : kcChk p ws = true) : KC p σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have L := h.lay hF hp
  exact ⟨h.top.step L hP hc.1, by rw [L.keepBytes hP hc.2]; exact h.xi⟩

end

/-! ## Two runs -/

/-- Two runs in the layout, with the same pointers and stack pointer. -/
structure Two (p : Params) (S : Nat) (x y : State) : Prop where
  lx : Lay S kgR (kgW p) x
  ly : Lay S kgR (kgW p) y
  same : SameB x y

theorem kc_two {p : Params} (hF : PFacts p) {S : Nat} {σ₁ σ₂ x y : State} (p₁ : kgPre p S σ₁) (p₂ : kgPre p S σ₂)
    (pub : kgPub p S σ₁ σ₂) (h₁ : KC p σ₁ x) (h₂ : KC p σ₂ y) : Two p S x y := by
  obtain ⟨esp, _, e0, e1, e2, e3⟩ := kgPub_eq pub
  refine ⟨h₁.lay hF p₁, h₂.lay hF p₂, fun r hr => ?_, by rw [h₁.top.sp, h₂.top.sp, esp]⟩
  simp only [bases, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.top.x25, h₂.top.x25, e0]
  · rw [h₁.top.x26, h₂.top.x26, e1]
  · rw [h₁.top.x27, h₂.top.x27, e2]
  · rw [h₁.top.x28, h₂.top.x28, e3]

/-- A piece of code that keeps the layout, from two runs in it, leaves two runs in it. -/
theorem Two.step {p : Params} {S : Nat} {c : Prog isa} (htr : RelCT isa (Two p S) c fun _ _ => True)
    (hok : ∀ x, Lay S kgR (kgW p) x → WP isa c x fun x' => ∃ W, PostB S x x' W) :
    RelCT isa (Two p S) c (Two p S) :=
  RelCT.postDep htr (F := fun x x' => ∃ W, PostB S x x' W) (fun x y h => ⟨hok x h.lx, hok y h.ly⟩)
    fun x y x' y' h ⟨_, hx⟩ ⟨_, hy⟩ => ⟨h.lx.post hx, h.ly.post hy,
      fun r hr => by rw [hx.bs r (bases_kept r hr), hy.bs r (bases_kept r hr)]; exact h.same.1 r hr, by rw [hx.sp, hy.sp]; exact h.same.2⟩

theorem Two.x28 {p : Params} {S : Nat} {x y : State} (h : Two p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ [Reg.x28], x.gpr r = y.gpr r := ⟨h.same.2, fun r hr => by
  simp only [List.mem_singleton] at hr; subst hr; exact h.same.1 .x28 (by decide)⟩

theorem Two.bases {p : Params} {S : Nat} {x y : State} (h : Two p S x y) :
    x.sp = y.sp ∧ ∀ r ∈ bases, x.gpr r = y.gpr r := ⟨h.same.2, h.same.1⟩

/-! ## Pieces -/

/-- Two runs of the function, from entry states that satisfy the
precondition and agree on the public data, each related by `I` to its
entry state. -/
abbrev R (p : Params) (S : Nat) (I : State → State → Prop) : State → State → Prop :=
  Rel2 (kgPre p S) (kgPub p S) I

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure Piece (p : Params) (S : Nat) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, kgPre p S σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (R p S I) c fun _ _ => True

section
variable {p : Params} {S : Nat} {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : Piece p S I J c₁) (h₂ : Piece p S J K c₂) :
    Piece p S I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : Piece p S I J c)
    (hI : ∀ σ s, kgPre p S σ → I' σ s → I σ s) (hJ : ∀ σ s, kgPre p S σ → J σ s → J' σ s) :
    Piece p S I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece p S (I k) (I (k + 1)) (f k)) →
      Piece p S (I a) (I (a + n)) (seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (Q := fun k => R p S (I k)) n a fun k h₁ h₂ => relInv (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem rel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, kgPre p S σ₁ → kgPre p S σ₂ → kgPub p S σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (R p S I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

end

end VG.Proof.MlDsa.AArch64.KeyGen
