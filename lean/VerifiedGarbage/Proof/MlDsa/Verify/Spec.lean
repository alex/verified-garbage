import VerifiedGarbage.Proof.MlDsa.Verify.Bounds

/-!
# ML-DSA: `verifyMu` as the verification functions compute it

Untrusted: everything here is checked by Lean. The pieces of the public key
and of the signature (`vT1`, `vCt`, `vZ`, `vHint`) and the seeds of `Â`
(`aSeed`); and, once the hint is well formed and the samplers have given
`Â` and `c` within the bounds `b`, `verifyMu` computed row by row
(`verifyMu_rows`): row `r` of `w′` is `NTT⁻¹` of the sum of the products
`Â[r, s] ẑ[s]` from `s = 0` (`dotAcc`), less `ĉ t̂₁[r]`, and its `w′₁` the
`UseHint`s of `h[r]` and its coefficients.
-/

namespace VG.Proof.MlDsa.Verify

open VG.Spec.MlDsa

/-! ## The pieces of the inputs -/

section
variable (p : Params) (pk σ : List Byte)

/-- The length of a packed `z[i]`, `32(1 + bitlen (γ₁ - 1))` bytes. -/
def lenZ : Nat := 32 * (1 + bitlen (p.γ₁ - 1))

/-- `ρ`, the first 32 bytes of the public key. -/
def vRho : List Byte := pk.take 32

/-- `t₁[r]`. -/
def vT1 (r : Nat) : Vector Nat n := simpleBitUnpack ((pk.drop (32 + 320 * r)).take 320) t1Max

/-- `c̃`. -/
def vCt : List Byte := σ.take p.ctildeLen

/-- `z[i]`. -/
def vZ (i : Nat) : IPoly :=
  bitUnpack ((σ.drop (p.ctildeLen + lenZ p * i)).take (lenZ p)) (p.γ₁ - 1) p.γ₁

/-- `h`, or `⊥`. -/
def vHint : Option (List (Vector Bool n)) :=
  hintBitUnpack p.ω p.k ((σ.drop (p.ctildeLen + lenZ p * p.ℓ)).take (p.ω + p.k))

/-- The seed `ρ ‖ s ‖ r` of `Â[r, s]`. -/
def aSeed (r s : Nat) : List Byte := vRho pk ++ integerToBytes s 1 ++ integerToBytes r 1

end

theorem bitlen_q : bitlen (q - 1) = 23 := by decide

theorem pkDecode_eq (p : Params) (pk : List Byte) :
    pkDecode p pk = (vRho pk, (List.range p.k).map (vT1 pk)) := by
  unfold pkDecode
  rw [bitlen_q]
  rfl

theorem sigDecode_eq (p : Params) (σ : List Byte) :
    sigDecode p σ = (vCt p σ, (List.range p.ℓ).map (vZ p σ), vHint p σ) := by
  simp only [sigDecode, pieces, vCt, vHint, lenZ, List.map_map]
  rfl

/-! ## Row by row -/

/-- `mapM` of a function that succeeds everywhere. -/
theorem mapM_range {β : Type} {f : Nat → Option β} {g : Nat → β} :
    ∀ {k : Nat}, (∀ i < k, f i = some (g i)) → (List.range k).mapM f = some ((List.range k).map g)
  | 0, _ => rfl
  | k + 1, h => by
    rw [List.range_succ, List.mapM_append, mapM_range fun i hi => h i (by omega), List.mapM_cons,
      h k (by omega), List.map_append]
    rfl

theorem add_zero_left (f : Poly) : add zero f = f := by
  apply Vector.ext
  intro i hi
  simp only [add, zero, Vector.getElem_zipWith, Vector.getElem_replicate]
  exact Fin.ext (by rw [Fin.val_add]; simp)

section
variable (p : Params) (σ : List Byte) (A : Nat → Nat → Poly)

/-- `ẑ[i]`. -/
def zHat (i : Nat) : Poly := ntt (toRq (vZ p σ i))

/-- `Σ_{s < j} Â[r, s] ẑ[s]`, from `s = 0`. -/
def dotAcc (r : Nat) : Nat → Poly
  | 0 => zero
  | j + 1 => add (dotAcc r j) (multiplyNTT (A r j) (zHat p σ j))

end

/-- `t̂₁[r]`. -/
def t1Hat (pk : List Byte) (r : Nat) : Poly := ntt ((vT1 pk r).map fun c => ofInt (c * 2 ^ d : Nat))

section
variable (p : Params) (pk σ : List Byte) (A : Nat → Nat → Poly) (c : IPoly)

/-- Row `r` of `w′`. -/
def wRow (r : Nat) : Poly :=
  nttInv (sub (dotAcc p σ A r p.ℓ) (multiplyNTT (ntt (toRq c)) (t1Hat pk r)))

/-- Row `r` of `w′₁`, with the hint `h`. -/
def w1Row (h : List (Vector Bool n)) (r : Nat) : Vector Nat n :=
  Vector.zipWith (fun hj wj => (useHint p.γ₂ hj wj).toNat) (h.getD r (Vector.replicate n false))
    (wRow p pk σ A c r)

end

theorem foldl_dot (p : Params) (σ : List Byte) (A : Nat → Nat → Poly) (r : Nat) :
    ∀ j, ((List.range j).map fun s => multiplyNTT (A r s) (zHat p σ s)).foldl add zero = dotAcc p σ A r j
  | 0 => rfl
  | j + 1 => by
    rw [List.range_succ, List.map_append, List.foldl_append, foldl_dot p σ A r j]
    rfl

theorem zipWith_range {α β γ : Type} (f : α → β → γ) (g : Nat → α) (h : Nat → β) (k : Nat) :
    List.zipWith f ((List.range k).map g) ((List.range k).map h) = (List.range k).map fun i => f (g i) (h i) := by
  rw [List.zipWith_map, List.zipWith_self]

theorem zipWith_getD {α β γ : Type} (f : α → β → γ) (d : α) (l : List α) (g : Nat → β) {k : Nat}
    (hl : l.length = k) :
    List.zipWith f l ((List.range k).map g) = (List.range k).map fun i => f (l.getD i d) (g i) := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using h₁)]
  rfl

theorem some_bind' {α β : Type} (x : α) (f : α → Option β) : (some x >>= f) = f x := rfl

/-- `verifyMu`, once the hint is well formed and the samplers have given
`Â` and `c`. -/
theorem verifyMu_rows (p : Params) (b : Bounds) (pk μ σ : List Byte) {h : List (Vector Bool n)}
    (hh : vHint p σ = some h) (hl : h.length = p.k) {A : Nat → Nat → Poly}
    (hA : ∀ r < p.k, ∀ s < p.ℓ, rejNTTPoly b.rejNTT (aSeed pk r s) = some (A r s)) {c : IPoly}
    (hc : sampleInBall p.τ b.ball (vCt p σ) = some c) :
    verifyMu p b pk μ σ = some (decide (normR ((List.range p.ℓ).map (vZ p σ)) < p.γ₁ - p.β) &&
      vCt p σ == H (μ ++ (List.range p.k).flatMap fun r =>
        simpleBitPack (w1Row p pk σ A c h r) ((q - 1) / (2 * p.γ₂) - 1)) p.ctildeLen) := by
  have eA : expandA p b (vRho pk) = some ((List.range p.k).map fun r => (List.range p.ℓ).map (A r)) :=
    mapM_range fun r hr => mapM_range fun s hs => hA r hr s hs
  unfold verifyMu
  rw [pkDecode_eq, sigDecode_eq, hh]
  dsimp only
  rw [eA, hc]
  have e1 : ∀ r, List.zipWith multiplyNTT (List.map (A r) (List.range p.ℓ))
      (List.map (fun x => ntt (toRq (vZ p σ x))) (List.range p.ℓ)) =
      (List.range p.ℓ).map fun s => multiplyNTT (A r s) (zHat p σ s) := fun r => zipWith_range _ _ _ _
  simp only [some_bind', List.map_map, w1Encode, matrixVectorNTT, scalarVectorNTT, subVec, Function.comp_def, e1,
    foldl_dot]
  rw [zipWith_range, List.map_map, zipWith_getD _ (Vector.replicate n false) _ _ hl, List.flatMap_map]
  simp only [Function.comp_apply, w1Row, wRow, t1Hat]
  rfl

end VG.Proof.MlDsa.Verify
