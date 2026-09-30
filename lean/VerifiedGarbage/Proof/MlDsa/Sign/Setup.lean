import VerifiedGarbage.Proof.MlDsa.Sign.Iter
import VerifiedGarbage.Proof.MlDsa.Sign.Leak

/-!
# ML-DSA: signing's matrix and private key, polynomial by polynomial

Untrusted: everything here is checked by Lean. The vectors that
`skDecode` gives, transformed by `NTT` as `Sign_internal` uses them, are
`List.range` mapped by a function of the index of the piece of the private
key (`skS1_eq`, `skS2_eq`, `skT0_eq`); `ExpandA` is the matrix of its
entries if each `RejNTTPoly` finishes (`expandA_some`), and fails if one
does not (`expandA_none`). With them, `signMu` and `signLeakT` in terms of
the loop (`signMu_some`, `signMu_none`, `signLeakT_eq`).
-/

namespace VG.Proof.MlDsa.Sign

open VG.Spec.MlDsa

/-! ## The private key -/

section
variable (p : Params) (sk : List Byte)

/-- The length of the encoding of a polynomial of `s₁` or `s₂`. -/
abbrev lenS : Nat := 32 * bitlen (2 * p.η)

/-- `ŝ₁[r] = NTT(BitUnpack(sk[128 + lenS·r : …], η, η))`. -/
def s1F (r : Nat) : Poly := ntt (toRq (bitUnpack ((sk.drop (128 + lenS p * r)).take (lenS p)) p.η p.η))

/-- `ŝ₂[i]`. -/
def s2F (i : Nat) : Poly :=
  ntt (toRq (bitUnpack ((sk.drop (128 + lenS p * p.ℓ + lenS p * i)).take (lenS p)) p.η p.η))

/-- `t̂₀[i]`. -/
def t0F (i : Nat) : Poly :=
  ntt (toRq (bitUnpack ((sk.drop (128 + lenS p * p.ℓ + lenS p * p.k + 32 * d * i)).take (32 * d))
    (2 ^ (d - 1) - 1) (2 ^ (d - 1))))

theorem skS1_eq : (skDecode p sk).2.2.2.1.map (fun s => ntt (toRq s)) = (List.range p.ℓ).map (s1F p sk) := by
  simp only [skDecode, pieces, List.map_map]; rfl

theorem skS2_eq : (skDecode p sk).2.2.2.2.1.map (fun s => ntt (toRq s)) = (List.range p.k).map (s2F p sk) := by
  simp only [skDecode, pieces, List.map_map]; rfl

theorem skT0_eq : (skDecode p sk).2.2.2.2.2.map (fun s => ntt (toRq s)) = (List.range p.k).map (t0F p sk) := by
  simp only [skDecode, pieces, List.map_map]; rfl

theorem skRho_eq : (skDecode p sk).1 = sk.take 32 := rfl

theorem skK_eq : (skDecode p sk).2.1 = (sk.drop 32).take 32 := rfl

end

/-! ## `ExpandA` -/

/-- The seed `ρ ‖ IntegerToBytes(j, 1) ‖ IntegerToBytes(i, 1)` of `Â[i, j]`. -/
def aSeed (ρ : List Byte) (i j : Nat) : List Byte := ρ ++ integerToBytes j 1 ++ integerToBytes i 1

/-- `Â[i, j]`, if its `RejNTTPoly` finishes within `bound` bytes. -/
def aF (bound : Nat) (ρ : List Byte) (i j : Nat) : Poly := (rejNTTPoly bound (aSeed ρ i j)).getD zero

theorem mapM_eq_some_of {α β : Type} {f : α → Option β} {g : α → β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = some (g x)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x (List.mem_cons_self ..), mapM_eq_some_of fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem mapM_eq_none_of {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, (∃ x ∈ l, f x = none) → l.mapM f = none
  | [], ⟨_, h, _⟩ => absurd h List.not_mem_nil
  | x :: l, ⟨y, hy, hn⟩ => by
    rw [List.mapM_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hn]; rfl
    · cases f x with
      | none => rfl
      | some _ => simp only [Option.bind_eq_bind, Option.bind_some]; rw [mapM_eq_none_of ⟨y, hy, hn⟩]; rfl

theorem expandA_some {p : Params} {b : Bounds} {ρ : List Byte}
    (h : ∀ i < p.k, ∀ j < p.ℓ, (rejNTTPoly b.rejNTT (aSeed ρ i j)).isSome) :
    expandA p b ρ = some (amat p (aF b.rejNTT ρ)) := by
  unfold expandA amat
  refine mapM_eq_some_of fun i hi => mapM_eq_some_of fun j hj => ?_
  rw [List.mem_range] at hi hj
  have := h i hi j hj
  unfold aF
  show rejNTTPoly b.rejNTT (aSeed ρ i j) = some ((rejNTTPoly b.rejNTT (aSeed ρ i j)).getD zero)
  cases e : rejNTTPoly b.rejNTT (aSeed ρ i j) with
  | none => rw [e] at this; cases this
  | some x => rfl

theorem expandA_none {p : Params} {b : Bounds} {ρ : List Byte}
    (h : ∃ i < p.k, ∃ j < p.ℓ, rejNTTPoly b.rejNTT (aSeed ρ i j) = none) : expandA p b ρ = none := by
  obtain ⟨i, hi, j, hj, hn⟩ := h
  exact mapM_eq_none_of ⟨i, List.mem_range.mpr hi, mapM_eq_none_of ⟨j, List.mem_range.mpr hj, hn⟩⟩

/-! ## `Sign_internal` -/

section
variable {p : Params} {sk μ rnd : List Byte}

/-- The signature, from the loop's result. -/
def sigOf (p : Params) (r : List Byte × List Poly × List (Vector Bool n)) : List Byte :=
  sigEncode p r.1 (r.2.1.map fun zi => zi.map fun c => modPm c.val q) r.2.2

theorem signMu_some {b : Bounds} {Â : List (List Poly)} (hA : expandA p b (sk.take 32) = some Â)
    {r : List Byte × List Poly × List (Vector Bool n)}
    (hL : signLoop p b Â ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
      ((List.range p.k).map (t0F p sk)) μ (H ((sk.drop 32).take 32 ++ rnd ++ μ) 64) b.sign 0 = some r) :
    signMu p b sk μ rnd = some (sigOf p r) := by
  rw [signMu_eq, skRho_eq, hA, Option.bind_some, skS1_eq, skS2_eq, skT0_eq, skK_eq, hL]; rfl

theorem signMu_none_A {b : Bounds} (hA : expandA p b (sk.take 32) = none) : signMu p b sk μ rnd = none := by
  rw [signMu_eq, skRho_eq, hA]; rfl

theorem signMu_none_L {b : Bounds} {Â : List (List Poly)} (hA : expandA p b (sk.take 32) = some Â)
    (hL : signLoop p b Â ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
      ((List.range p.k).map (t0F p sk)) μ (H ((sk.drop 32).take 32 ++ rnd ++ μ) 64) b.sign 0 = none) :
    signMu p b sk μ rnd = none := by
  rw [signMu_eq, skRho_eq, hA, Option.bind_some, skS1_eq, skS2_eq, skT0_eq, skK_eq, hL]; rfl

/-- What signing leaks, once `ExpandA` finishes. -/
theorem signLeakT_eq {Â : List (List Poly)} (hA : expandA p maxBounds (sk.take 32) = some Â) :
    signLeakT p sk μ rnd = leakBytes (sk.take 32) ++
      signLeakLoopT p maxBounds Â ((List.range p.ℓ).map (s1F p sk)) ((List.range p.k).map (s2F p sk))
        ((List.range p.k).map (t0F p sk)) μ (H ((sk.drop 32).take 32 ++ rnd ++ μ) 64) maxBounds.sign 0 := by
  have h1 := skS1_eq p sk
  have h2 := skS2_eq p sk
  have h3 := skT0_eq p sk
  unfold signLeakT
  rcases e : skDecode p sk with ⟨ρ, K, tr, s₁, s₂, t₀⟩
  rw [e] at h1 h2 h3
  have hρ : ρ = sk.take 32 := by rw [← skRho_eq p sk, e]
  have hK : K = (sk.drop 32).take 32 := by rw [← skK_eq p sk, e]
  dsimp only at h1 h2 h3 ⊢
  subst hρ hK
  rw [hA, h1, h2, h3]

end

end VG.Proof.MlDsa.Sign
