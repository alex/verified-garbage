import VerifiedGarbage.Spec.Sha3
import VerifiedGarbage.Impl.Sha3.Tables

/-!
# SHA-3: lemmas about the specification

Untrusted: everything here is checked by Lean.

A round of Keccak-f[1600] lane by lane, in the form the implementations
compute it (`out`): the column parities `C`, `D`, the lanes `B` of
`π(ρ(θ(A)))` plane by plane, and χ and ι.
-/

namespace VG.Proof.Sha3

open VG.Spec.Sha3
open VG.Impl.Sha3 (rhoOff piSrc)

/-! ## ρ's offsets -/

/-- The rotation Algorithm 2 gives lane `j`. -/
def rhoSpec (j : Nat) : Nat :=
  match (List.range 24).find? (fun t => rhoPos t == (j % 5, j / 5)) with
  | some t => (t + 1) * (t + 2) / 2 % 64
  | none => 0

theorem rhoSpec_eq : ∀ j < 25, rhoSpec j = rhoOff j := by decide

theorem rhoOff_lt : ∀ j < 25, rhoOff j < 64 := by decide

theorem rotateLeft_zero (x : Lane) : x.rotateLeft 0 = x := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft]
  split <;> (try congr 1) <;> omega

theorem rho_get (A : State) {j : Nat} (hj : j < 25) :
    (rho A)[j] = A[j].rotateLeft (rhoOff j) := by
  rw [← rhoSpec_eq j hj]
  simp only [rho, Vector.getElem_ofFn, rhoSpec]
  cases (List.range 24).find? (fun t => rhoPos t == (j % 5, j / 5)) <;>
    simp [BitVec.rotateLeft_mod_eq_rotateLeft, rotateLeft_zero]

/-! ## A round, lane by lane -/

/-- `C[x]`. -/
def C (A : State) (x : Nat) : Lane := A[x]! ^^^ A[x + 5]! ^^^ A[x + 10]! ^^^ A[x + 15]! ^^^ A[x + 20]!

/-- `D[x]`, as `ROTR⁶³(C[x + 1]) ⊕ C[x - 1]`. -/
def D (A : State) (x : Nat) : Lane := (C A ((x + 1) % 5)).rotateRight 63 ^^^ C A ((x + 4) % 5)

/-- A rotation left by `k < 64`, as a rotation right (none for `k = 0`). -/
def rotl (v : Lane) (k : Nat) : Lane := if k = 0 then v else v.rotateRight (64 - k)

/-- Lane `x` of plane `y` of `π(ρ(θ(A)))`. -/
def B (A : State) (x y : Nat) : Lane := rotl (A[piSrc x y]! ^^^ D A ((x + 3 * y) % 5)) (rhoOff (piSrc x y))

/-- Lane `(x, y)` of `Rnd(A)` with round constant `rc`. -/
def out (A : State) (rc : Lane) (x y : Nat) : Lane :=
  let t := (B A ((x + 1) % 5) y ^^^ 0xffffffffffffffff) &&& B A ((x + 2) % 5) y ^^^ B A x y
  if x = 0 ∧ y = 0 then t ^^^ rc else t

/-- `ROTLᵏ` is a rotation right by `64 - k`. -/
theorem rotateLeft_eq (x : Lane) {k : Nat} (hk : 0 < k) (hk' : k < 64) :
    x.rotateLeft k = x.rotateRight (64 - k) := by
  ext i hi
  simp only [BitVec.getElem_rotateLeft, BitVec.getElem_rotateRight]
  split <;> split <;> (try congr 1) <;> omega

theorem rotl_eq (v : Lane) {k : Nat} (hk : k < 64) : rotl v k = v.rotateLeft k := by
  unfold rotl
  split
  · subst_vars; rw [rotateLeft_zero]
  · rw [rotateLeft_eq _ (by omega) hk]

theorem getElem!_eq (A : State) {i : Nat} (hi : i < 25) : A[i]! = A[i] := by
  simp [hi]

theorem lane_mod (A : State) {x : Nat} (hx : x < 5) (y : Nat) (hy : y < 5) :
    lane A x y = A[x + 5 * y]! := by
  simp only [lane, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem theta_get (A : State) {j : Nat} (hj : j < 25) : (theta A)[j] = A[j] ^^^ D A (j % 5) := by
  have hC : ∀ x, x < 5 → lane A x 0 ^^^ lane A x 1 ^^^ lane A x 2 ^^^ lane A x 3 ^^^ lane A x 4 =
      C A x := fun x hx => by
    simp only [lane_mod A hx _ (by decide : 0 < 5), lane_mod A hx _ (by decide : 1 < 5),
      lane_mod A hx _ (by decide : 2 < 5), lane_mod A hx _ (by decide : 3 < 5),
      lane_mod A hx _ (by decide : 4 < 5), C]
    rfl
  simp only [theta, Vector.getElem_ofFn]
  rw [hC _ (Nat.mod_lt _ (by omega)), hC _ (Nat.mod_lt _ (by omega)), D,
    rotateLeft_eq _ (by decide) (by decide), BitVec.xor_comm (C A _)]
  rfl

theorem B_eq (A : State) {x y : Nat} (hx : x < 5) (_hy : y < 5) :
    B A x y = (rho (theta A))[piSrc x y]'(by simp only [piSrc]; omega) := by
  have hj : piSrc x y < 25 := by simp only [piSrc]; omega
  rw [rho_get _ hj, theta_get _ hj, B, rotl_eq _ (rhoOff_lt _ hj), getElem!_eq _ hj]
  congr 3
  simp only [piSrc]; omega

theorem pi_get (R : State) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (pi R)[x + 5 * y]'(by omega) = R[piSrc x y]'(by simp only [piSrc]; omega) := by
  simp only [pi, Vector.getElem_ofFn, lane]
  rw [getElem!_eq _ (by omega)]
  congr 1
  simp only [piSrc]
  rw [show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega, Nat.mod_eq_of_lt hx]

theorem chi_get (P : State) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (chi P)[x + 5 * y]'(by omega) =
      P[x + 5 * y]'(by omega) ^^^
        (~~~(P[(x + 1) % 5 + 5 * y]'(by omega)) &&& P[(x + 2) % 5 + 5 * y]'(by omega)) := by
  simp only [chi, Vector.getElem_ofFn]
  rw [show (x + 5 * y) % 5 = x by omega, show (x + 5 * y) / 5 = y by omega]
  simp only [lane, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hx]
  rw [getElem!_eq _ (by omega), getElem!_eq _ (by omega), getElem!_eq _ (by omega)]

theorem rnd_get (A : State) (ir : Nat) {x y : Nat} (hx : x < 5) (hy : y < 5) :
    (rnd A ir)[x + 5 * y]'(by omega) = out A (RC ir) x y := by
  have hP : ∀ x' (hx' : x' < 5), (pi (rho (theta A)))[x' + 5 * y]'(by omega) = B A x' y := fun x' hx' => by
    rw [pi_get _ hx' hy, B_eq _ hx' hy]
  have hchi := chi_get (pi (rho (theta A))) hx hy
  rw [hP x hx, hP _ (Nat.mod_lt _ (by omega)), hP _ (Nat.mod_lt _ (by omega))] at hchi
  have hnot : ∀ v : Lane, ~~~v = v ^^^ 0xffffffffffffffff := fun v => by
    rw [BitVec.xor_comm]; rfl
  simp only [rnd, iota, out]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp only [Vector.getElem_set_self, and_self, ite_true]
    rw [show (chi (pi (rho (theta A))))[0] = (chi (pi (rho (theta A))))[0 + 5 * 0] from rfl, hchi,
      hnot, BitVec.xor_comm (B A 0 0)]
  · rw [Vector.getElem_set_ne _ _ (by omega), hchi, hnot, BitVec.xor_comm (B A x y)]
    simp only [h0, ite_false]

end VG.Proof.Sha3
