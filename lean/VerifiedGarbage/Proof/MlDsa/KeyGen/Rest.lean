import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.KeyGen.Poly

/-!
# ML-DSA key generation: the keys from the sampled polynomials

Lines 5–10 of Algorithm 6 (`kgRest`) on the entries `A (ℓr + s)` of `Â` and `S
r` of `s₁ ‖ s₂`, row by row of `t` (`tK`), as the keys are computed: `t[i]` is
`NTT⁻¹` of the sum of the products `Â[i, j] ŝ₁[j]` (`dotK`, from `j = 0`) plus
`s₂[i]`, the public key is `ρ` followed by the packed `t₁[i]` (`pkK`), and the
private key `ρ ‖ K ‖ tr` followed by the packed `s₁ ‖ s₂` and `t₀[i]` (`skK`)
(`kgRest_eq`).
-/

namespace VG.Proof.MlDsa.KeyGen

open VG.Spec.MlDsa

section
variable (p : Params) (A : Nat → Poly) (S : Nat → IPoly)

/-- `Σ_{j' < j} Â[i, j'] ŝ₁[j']`, summed from `j' = 0`. -/
def dotK (i j : Nat) : Poly :=
  ((List.range j).map fun j' => multiplyNTT (A (p.ℓ * i + j')) (ntt (toRq (S j')))).foldl add zero

/-- `t[i]`. -/
def tK (i : Nat) : Poly := add (nttInv (dotK p A S i p.ℓ)) (toRq (S (p.ℓ + i)))

def t1K (i : Nat) : Vector Nat n := (tK p A S i).map fun c => (power2Round c).1.toNat
def t0K (i : Nat) : IPoly := (tK p A S i).map fun c => (power2Round c).2

def pkK (ρ : List Byte) : List Byte := ρ ++ (List.range p.k).flatMap fun i => simpleBitPack (t1K p A S i) t1Max

def skK (ρ K : List Byte) : List Byte :=
  ρ ++ K ++ H (pkK p A S ρ) 64 ++ (List.range (p.ℓ + p.k)).flatMap (fun r => bitPack (S r) p.η p.η) ++
    (List.range p.k).flatMap fun i => bitPack (t0K p A S i) (2 ^ (d - 1) - 1) (2 ^ (d - 1))

theorem dotK_succ (i j : Nat) :
    dotK p A S i (j + 1) = add (dotK p A S i j) (multiplyNTT (A (p.ℓ * i + j)) (ntt (toRq (S j)))) := by
  simp only [dotK, List.range_succ, List.map_append, List.map_cons, List.map_nil, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem dotK_one (i : Nat) : dotK p A S i 1 = multiplyNTT (A (p.ℓ * i)) (ntt (toRq (S 0))) := by
  rw [dotK_succ, show dotK p A S i 0 = zero from rfl, add_zero_left, Nat.add_zero]

theorem zipWith_map_map {α β γ : Type} (f : α → β → γ) (g : Nat → α) (h : Nat → β) (k : Nat) :
    List.zipWith f ((List.range k).map g) ((List.range k).map h) = (List.range k).map fun j => f (g j) (h j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.zipWith_append (by simp), ih]
    simp

theorem kgRest_eq (ρ K : List Byte) :
    kgRest p ρ K ((List.range p.k).map fun r => (List.range p.ℓ).map fun s => A (p.ℓ * r + s))
      ((List.range p.ℓ).map S) ((List.range p.k).map fun r => S (r + p.ℓ)) = (pkK p A S ρ, skK p A S ρ K) := by
  have ht : addVec ((matrixVectorNTT ((List.range p.k).map fun r => (List.range p.ℓ).map fun s => A (p.ℓ * r + s))
      (((List.range p.ℓ).map S).map fun s => ntt (toRq s))).map nttInv) (((List.range p.k).map fun r => S (r + p.ℓ)).map toRq) =
      (List.range p.k).map (tK p A S) := by
    simp only [matrixVectorNTT, addVec, List.map_map]
    rw [zipWith_map_map]
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp, tK, dotK, Nat.add_comm i p.ℓ]
    rw [zipWith_map_map]
    rfl
  unfold kgRest
  dsimp only
  rw [ht]
  simp only [pkK, skK, t1K, t0K, skEncode, pkEncode, List.map_map, List.flatMap_map, List.range_add,
    List.flatMap_append, List.append_assoc]
  simp only [Function.comp, Nat.add_comm]

end

/-- Bytes in pieces of `len`. -/
theorem bytesAt_pieces (m : Mem) (a : Addr) (o len : Nat) :
    ∀ k, Spec.Sha3.bytesAt m (a + BitVec.ofNat 64 o) (len * k) =
      (List.range k).flatMap fun i => Spec.Sha3.bytesAt m (a + BitVec.ofNat 64 (o + len * i)) len
  | 0 => rfl
  | k + 1 => by
    rw [Nat.mul_succ, Proof.MlKem.bytesAt_add, bytesAt_pieces m a o len k, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, BitVec.add_assoc, ← BitVec.ofNat_add]

end VG.Proof.MlDsa.KeyGen
