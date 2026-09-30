import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Mask
import VerifiedGarbage.Proof.MlDsa.KeyGen.Leak

/-!
# ML-DSA key generation on x86-64: what holds throughout, and pieces

Untrusted: everything here is checked by Lean. What holds of the state
throughout (`KC`: `Top`, the seed `ξ` at `seed`, and MXCSR's control bits),
and a piece of code (`Piece p I J c`): it takes each run from `I` to `J`
(`ok`), and two runs related by `I` leak the same (`tr`). Pieces compose
(`Piece.seq`, `Piece.seqR`), which proves correctness and constant time
together.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc seqR)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params keyGenSeeds)
open VG.Spec.Sha3 (bytesAt)

/-! ## The seed and what it gives -/

/-- `ξ`. -/
abbrev xiOf (σ : State) : List Byte := bytesAt σ.mem (σ.gpr .rdi) 32
/-- `ρ`, `ρ′` and `K`. -/
abbrev rhoOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).1
abbrev rho'Of (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.1
abbrev kOf (p : Params) (σ : State) : List Byte := (keyGenSeeds p (xiOf σ)).2.2

/-! ## What holds throughout -/

/-- What holds throughout, from the entry state `σ`. -/
structure KC (p : Params) (σ s : State) : Prop where
  top : Top kgM σ s
  xi : bytesAt s.mem (pa s (.rbp, 0)) 32 = xiOf σ
  mx : MX s = MX σ

/-- A piece that writes `ws` keeps `KC`. -/
def kcChk (p : Params) (ws : List (Ptr × Nat)) : Bool := topChk (kgB p) ws && keepB (kgB p) ws (.rbp, 0) 32

section
variable {p : Params} (hF : PFacts p) {σ : State} (hp : (kgK p).pre σ)
include hF hp

theorem KC.lay {s : State} (h : KC p σ s) : Lay kgR (kgW p) s := kgLay hF hp h.top

theorem KC.site {s : State} (h : KC p σ s) : Site p s := ⟨h.lay hF hp, by rw [h.top.rsp]; exact hp.1⟩

theorem KC.step {s s' : State} (h : KC p σ s) {ws : List (Ptr × Nat)} (hP : PPostB s s' ws) (hx : MX s' = MX s)
    (hc : kcChk p ws = true) : KC p σ s' := by
  simp only [kcChk, Bool.and_eq_true] at hc
  have L := h.lay hF hp
  exact ⟨h.top.step L hP kgM_bases hc.1, by rw [L.keepBytes hP hc.2]; exact h.xi, hx.trans h.mx⟩

end

theorem kc_two {p : Params} (hF : PFacts p) {σ₁ σ₂ x y : State} (p₁ : (kgK p).pre σ₁) (p₂ : (kgK p).pre σ₂)
    (pub : (kgK p).pub σ₁ σ₂) (h₁ : KC p σ₁ x) (h₂ : KC p σ₂ y) : Two p x y := by
  obtain ⟨e1, e2, e3, e4, e5, _⟩ := pub
  refine ⟨h₁.site hF p₁, h₂.site hF p₂, fun r hr => ?_, by rw [h₁.top.rsp, h₂.top.rsp, e5]⟩
  simp only [kgRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h₁.top.regs (.rbx, .rcx) (by decide), h₂.top.regs (.rbx, .rcx) (by decide), e4]
  · rw [h₁.top.regs (.rbp, .rdi) (by decide), h₂.top.regs (.rbp, .rdi) (by decide), e1]
  · rw [h₁.top.regs (.r12, .rsi) (by decide), h₂.top.regs (.r12, .rsi) (by decide), e2]
  · rw [h₁.top.regs (.r13, .rdx) (by decide), h₂.top.regs (.r13, .rdx) (by decide), e3]

/-! ## Pieces -/

/-- Two runs of the function, from entry states that satisfy the
precondition and agree on the public data, each related by `I` to its
entry state. -/
abbrev R (p : Params) (I : State → State → Prop) : State → State → Prop := Rel2 (kgK p).pre (kgK p).pub I

/-- `c` takes each run from `I` to `J`, and leaks the same in two runs related by `I`. -/
structure Piece (p : Params) (I J : State → State → Prop) (c : Prog isa) : Prop where
  ok : ∀ σ s, (kgK p).pre σ → I σ s → WP isa c s (J σ)
  tr : RelCT isa (R p I) c fun _ _ => True

section
variable {p : Params} {I J K : State → State → Prop}

theorem Piece.seq {c₁ c₂ : Prog isa} (h₁ : Piece p I J c₁) (h₂ : Piece p J K c₂) : Piece p I K (.seq c₁ c₂) :=
  ⟨fun σ s hp hs => WP.seq (WP.mono (h₁.ok σ s hp hs) fun s' h => h₂.ok σ s' hp h),
    RelCT.seq (relInv h₁.ok h₁.tr) h₂.tr⟩

theorem Piece.mono {c : Prog isa} {I' J' : State → State → Prop} (h : Piece p I J c)
    (hI : ∀ σ s, (kgK p).pre σ → I' σ s → I σ s) (hJ : ∀ σ s, (kgK p).pre σ → J σ s → J' σ s) :
    Piece p I' J' c :=
  ⟨fun σ s hp hs => WP.mono (h.ok σ s hp (hI σ s hp hs)) fun s' h => hJ σ s' hp h,
    RelCT.mono h.tr (fun _ _ ⟨σ₁, σ₂, p₁, p₂, pub, i₁, i₂⟩ => ⟨σ₁, σ₂, p₁, p₂, pub, hI _ _ p₁ i₁, hI _ _ p₂ i₂⟩)
      fun _ _ h => h⟩

theorem Piece.seqR {f : Nat → Prog isa} {I : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → Piece p (I k) (I (k + 1)) (f k)) →
      Piece p (I a) (I (a + n)) (seqR f a n)
  | n, a, h =>
    ⟨fun σ s hp hs => seqR_ok (I := fun k => I k σ) n a (fun k h₁ h₂ s hs => (h k h₁ h₂).ok σ s hp hs) s hs,
      RelCT.mono (seqR_tr (R := fun k => R p (I k)) n a fun k h₁ h₂ => relInv (h k h₁ h₂).ok (h k h₁ h₂).tr)
        (fun _ _ h => h) fun _ _ _ => trivial⟩

/-- A piece's constant time, from a relation implied by the invariants of two runs. -/
theorem rel_of {c : Prog isa} {Q : State → State → Prop} (htr : RelCT isa Q c fun _ _ => True)
    (h : ∀ σ₁ σ₂ x y, (kgK p).pre σ₁ → (kgK p).pre σ₂ → (kgK p).pub σ₁ σ₂ → I σ₁ x → I σ₂ y → Q x y) :
    RelCT isa (R p I) c fun _ _ => True :=
  RelCT.mono htr (fun _ _ ⟨_, _, p₁, p₂, hpub, i₁, i₂⟩ => h _ _ _ _ p₁ p₂ hpub i₁ i₂) fun _ _ h => h

end

end VG.Proof.MlDsa.X86_64.KeyGen
