import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Spec.MlKem.Expanded

/-!
# ML-KEM: expanded encapsulation keys, for every target

Untrusted: everything here is checked by Lean. A stored polynomial moves
with its bytes (`polyIs_move`), and the entries of a matrix that
`sampleMatrix` returns are those `SampleNTT` samples (`sampleMatrix_entry`).
And an expanded key of any encapsulation key exists (`expandedEk_ekxMem`),
for the satisfiability of the contracts that take one.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-! ## Polynomials moved with their bytes -/

theorem read_move {m m' : Mem} {a a' : Addr} {n : Nat}
    (h : ∀ i < n, m' (a' + BitVec.ofNat 64 i) = m (a + BitVec.ofNat 64 i)) :
    m'.read a' n = m.read a n := by
  induction n generalizing a a' with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih fun i hi => ?_]
    have := h (i + 1) (by omega)
    rwa [Offset.add_ofNat_succ, Offset.add_ofNat_succ] at this

theorem coeffAt_move {m m' : Mem} {p p' : Addr}
    (h : ∀ k < 1024, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) {i : Nat} (hi : i < n) :
    coeffAt m' p' i = coeffAt m p i := by
  rw [n_eq] at hi
  simp only [coeffAt, Mem.readW]
  rw [read_move fun j hj => ?_]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact h _ (by omega)

/-- A polynomial whose bytes are those of another. -/
theorem polyIs_move {m m' : Mem} {p p' : Addr} {f : Poly}
    (h : ∀ k < 1024, m' (p' + BitVec.ofNat 64 k) = m (p + BitVec.ofNat 64 k)) (hf : PolyIs m p f) :
    PolyIs m' p' f :=
  ⟨fun i hi => by rw [coeffAt_move h hi]; exact hf.1 i hi,
    (ext_getElem! fun i hi => by rw [polyAt_get _ _ hi, polyAt_get _ _ hi, coeffAt_move h hi]).trans hf.2⟩

/-- Polynomial `e` of `len` bytes copied from `a` to `a'`. -/
theorem polyIs_copied {m m' : Mem} {a a' : Addr} {len : Nat} (h : bytesAt m' a' len = bytesAt m a len)
    {e : Nat} (he : 1024 * e + 1024 ≤ len) {f : Poly} (hf : PolyIs m (a + BitVec.ofNat 64 (1024 * e)) f) :
    PolyIs m' (a' + BitVec.ofNat 64 (1024 * e)) f := by
  refine polyIs_move (fun k hk => ?_) hf
  have := congrArg (fun L => L[1024 * e + k]?) h
  simp only [bytesAt, List.getElem?_map, List.getElem?_range (show 1024 * e + k < len by omega), Option.map_some,
    Option.some.injEq] at this
  rwa [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]

/-! ## The entries of a sampled matrix -/

theorem mapM_some_getD {α β : Type} {f : α → Option β} (d : β) :
    ∀ {L : List α} {B : List β}, L.mapM f = some B → ∀ i (hi : i < L.length), f L[i] = some (B.getD i d)
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | x :: L, B, h, i, hi => by
    rw [List.mapM_cons] at h
    cases hx : f x with
    | none => rw [hx] at h; cases h
    | some b =>
      cases hL : L.mapM f with
      | none => rw [hx, hL] at h; cases h
      | some B' =>
        rw [hx, hL] at h
        cases h
        cases i with
        | zero => exact hx
        | succ i => exact mapM_some_getD d hL i (by simp only [List.length_cons] at hi; omega)

/-- Entry `(i, j)` of the matrix `sampleMatrix` returns. -/
theorem sampleMatrix_entry {k iters : Nat} {ρ : List Byte} {A : List (List Poly)}
    (h : sampleMatrix k iters ρ = some A) {i j : Nat} (hi : i < k) (hj : j < k) :
    sampleNTT iters (matSeed ρ i j) = some ((A.getD i []).getD j zero) := by
  have hrow := mapM_some_getD [] h i (by rw [List.length_range]; exact hi)
  rw [List.getElem_range] at hrow
  have := mapM_some_getD zero hrow j (by rw [List.length_range]; exact hj)
  rwa [List.getElem_range] at this

/-! ## An expanded key in memory -/

private theorem ifp {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) : (if c then a else b) = a :=
  ite_eq_left_iff.mpr fun h' => absurd h h'

private theorem ifn {α : Sort _} {c : Prop} [Decidable c] (h : ¬ c) (a b : α) : (if c then a else b) = b :=
  ite_eq_right_iff.mpr fun h' => absurd h' h

/-- Byte `t` of `f` stored as `[u32; 256]`. -/
def polyByte (f : Poly) (t : Nat) : Byte :=
  (BitVec.ofNat 32 (f[t / 4]!).val).extractLsb' (8 * (t % 4)) 8

theorem polyIs_of_polyByte {m : Mem} {p : Addr} {f : Poly}
    (h : ∀ t < 1024, m (p + BitVec.ofNat 64 t) = polyByte f t) : PolyIs m p f := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [n_eq] at hi
  simp only [coeffAt, Mem.readW]
  rw [Mem.read_eq_of_bytes (v := BitVec.ofNat 32 (f[i]!).val) fun j hj => ?_]
  · exact BitVec.setWidth_eq _
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add, h _ (by omega), polyByte,
      show (4 * i + j) / 4 = i by omega, show (4 * i + j) % 4 = j by omega]

open Classical in
/-- The matrix `SampleNTT` samples from `ρ` for any bound for which it
samples one (all give the same), or zeros if there is none. -/
noncomputable def limMatrix (k : Nat) (ρ : List Byte) (i j : Nat) : Poly :=
  if h : ∃ iters A, sampleMatrix k iters ρ = some A then
    (((Classical.choose_spec h).choose).getD i []).getD j zero
  else zero

theorem limMatrix_eq {k iters : Nat} {ρ : List Byte} {A : List (List Poly)}
    (h : sampleMatrix k iters ρ = some A) (i j : Nat) : limMatrix k ρ i j = (A.getD i []).getD j zero := by
  have hh : ∃ iters A, sampleMatrix k iters ρ = some A := ⟨iters, A, h⟩
  unfold limMatrix
  split
  · rename_i h'
    have h₂ := (Classical.choose_spec h').choose_spec
    have e₁ := sampleMatrix_mono k ρ h (Nat.le_max_left iters (Classical.choose h'))
    have e₂ := sampleMatrix_mono k ρ h₂ (Nat.le_max_right iters (Classical.choose h'))
    rw [e₁] at e₂
    rw [Option.some.inj e₂]
  · exact absurd hh ‹_›

/-- Byte `t` of an expanded key of `ek` with the entries `M`. -/
def ekxByte (p : Params) (ek : List Byte) (M : Nat → Nat → Poly) (t : Nat) : Byte :=
  if t < p.ekLen then ek.getD t 0
  else if t < p.ekLen + 32 then (H ek).getD (t - p.ekLen) 0
  else polyByte (M ((t - (p.ekLen + 32)) / 1024 / p.k) ((t - (p.ekLen + 32)) / 1024 % p.k))
    ((t - (p.ekLen + 32)) % 1024)

/-- Memory holding an expanded key of `ek` with the entries `M` at `x`, and zeros elsewhere. -/
def ekxMem (p : Params) (x : Addr) (ek : List Byte) (M : Nat → Nat → Poly) : Mem := fun a =>
  if (a - x).toNat < p.ekxLen then ekxByte p ek M (a - x).toNat else 0

theorem ekxMem_at {p : Params} {x : Addr} {ek : List Byte} {M : Nat → Nat → Poly} {t : Nat}
    (ht : t < p.ekxLen) (hl : p.ekxLen < 2 ^ 64) : ekxMem p x ek M (x + BitVec.ofNat 64 t) = ekxByte p ek M t := by
  simp only [ekxMem, Mem.sub_ofNat_toNat x (show t < 2 ^ 64 by omega), ht, ite_true]

theorem bytesAt_ext {m : Mem} {x : Addr} {len : Nat} {L : List Byte} (hl : L.length = len)
    (h : ∀ t < len, m (x + BitVec.ofNat 64 t) = L.getD t 0) : bytesAt m x len = L := by
  refine List.ext_getElem (by simp [bytesAt, hl]) fun t h₁ h₂ => ?_
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [h t (by simp [bytesAt] at h₁; exact h₁), List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₂]
  rfl

/-- An expanded key of `ek`, with the matrix `limMatrix`. -/
theorem expandedEk_ekxMem (p : Params) (x : Addr) {ek : List Byte} (hek : ek.length = p.ekLen) (hk : 0 < p.k)
    (hl : p.ekxLen < 2 ^ 64) : ExpandedEk p (ekxMem p x ek (limMatrix p.k (ekRho p ek))) x ek := by
  have hL : p.ekxLen = p.ekLen + 32 + 1024 * (p.k * p.k) := rfl
  have hA : ∀ i < p.k, ∀ j < p.k,
      PolyIs (ekxMem p x ek (limMatrix p.k (ekRho p ek))) (x + BitVec.ofNat 64 (p.ekxA i j))
        (limMatrix p.k (ekRho p ek) i j) := fun i hi j hj => by
    have hij : p.k * i + j < p.k * p.k := by
      have := Nat.mul_le_mul_left p.k (show i + 1 ≤ p.k by omega)
      rw [Nat.mul_succ] at this; omega
    refine polyIs_of_polyByte fun t ht => ?_
    have e : p.ekxA i j + t - (p.ekLen + 32) = 1024 * (p.k * i + j) + t := by
      simp only [Params.ekxA]; omega
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, ekxMem_at (by simp only [Params.ekxA]; omega) hl, ekxByte,
      ifn (by simp only [Params.ekxA]; omega), ifn (by simp only [Params.ekxA]; omega), e,
      show (1024 * (p.k * i + j) + t) / 1024 = p.k * i + j by omega,
      show (1024 * (p.k * i + j) + t) % 1024 = t by omega, Nat.mul_add_div hk, Nat.div_eq_of_lt hj,
      Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  refine ⟨bytesAt_ext hek fun t ht => ?_, bytesAt_ext (H_length ek) fun t ht => ?_,
    fun i hi j hj => (hA i hi j hj).1, fun iters A h i hi j hj => ?_⟩
  · rw [ekxMem_at (by omega) hl, ekxByte, ifp ht]
  · rw [BitVec.add_assoc, ← BitVec.ofNat_add, ekxMem_at (by omega) hl, ekxByte, ifn (by omega),
      ifp (by omega), Nat.add_sub_cancel_left]
  · rw [(hA i hi j hj).2, limMatrix_eq h]

end VG.Proof.MlKem
