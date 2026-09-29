import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Scrypt.Contract

/-!
# Facts about the Salsa20/8 Core specification

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Scrypt

open VG.Spec.Scrypt (Word step wordLE serialize bytesAt)

theorem rotateLeft_eq (x : Word) {k : Nat} (hk : 0 < k) (hk' : k < 32) :
    x.rotateLeft k = x.rotateRight (32 - k) := by
  rw [BitVec.rotateLeft_def, BitVec.rotateRight_def, Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt (by omega),
    show 32 - (32 - k) = k by omega, BitVec.or_comm]

/-! ## Lines with `Nat` indices -/

/-- An index `i < 16` as a `Fin 16`. -/
def fin (i : Nat) : Fin 16 := ⟨i % 16, Nat.mod_lt _ (by decide)⟩

/-- `step` with `Nat` indices. -/
def stepN (x : Vector Word 16) (i j k n : Nat) : Vector Word 16 := step x (fin i) (fin j) (fin k) n

theorem stepN_get (x : Vector Word 16) {i j k : Nat} (n : Nat) (hi : i < 16) (hj : j < 16)
    (hk : k < 16) (m : Nat) (hm : m < 16) :
    (stepN x i j k n)[m] = if i = m then x[i] ^^^ (x[j] + x[k]).rotateLeft n else x[m] := by
  simp only [stepN, step, fin, Vector.getElem_set, Fin.getElem_fin, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj,
    Nat.mod_eq_of_lt hk]

/-! ## Bytes and words -/

theorem eq_of_bytes32 {x y : BitVec 32}
    (h : ∀ j < 4, x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun z : BitVec 8 => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb'] at e
  simpa [Nat.mod_lt i (show 8 > 0 by omega), show 8 * (i / 8) + i % 8 = i by omega] using e

theorem bytesAt_getD (m : Mem) (p : Addr) {n i : Nat} (hi : i < n) :
    (bytesAt m p n).getD i 0 = m (p + BitVec.ofNat 64 i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi]

/-- A little-endian word as its bytes. -/
theorem readW32_eq (m : Mem) (a : Addr) :
    m.readW a 32 = m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a := by
  simp only [Mem.readW, Mem.read]
  rw [show a + 1 + 1 + 1 = a + 3 by rw [BitVec.add_assoc, BitVec.add_assoc]; rfl,
    show a + 1 + 1 = a + 2 by rw [BitVec.add_assoc]; rfl]
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, hi, decide_true, Bool.true_and]
  split
  · rfl
  split
  · rfl
  split
  · rfl
  simp only [show i - 8 - 8 - 8 < 8 by omega, ite_true]

/-- Word `j` of the bytes at `p` is the little-endian word at `p + 4j`. -/
theorem wordLE_bytesAt (m : Mem) (p : Addr) {n j : Nat} (hj : 4 * j + 4 ≤ n) :
    wordLE (bytesAt m p n) j = m.readW (p + BitVec.ofNat 64 (4 * j)) 32 := by
  rw [wordLE, bytesAt_getD _ _ (by omega), bytesAt_getD _ _ (by omega),
    bytesAt_getD _ _ (by omega), bytesAt_getD _ _ (by omega), readW32_eq]
  rw [show p + BitVec.ofNat 64 (4 * j + 3) = p + BitVec.ofNat 64 (4 * j) + 3 by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    show p + BitVec.ofNat 64 (4 * j + 2) = p + BitVec.ofNat 64 (4 * j) + 2 by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl,
    show p + BitVec.ofNat 64 (4 * j + 1) = p + BitVec.ofNat 64 (4 * j) + 1 by
      rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl]

theorem range_mul4 (g : Nat → Byte) : ∀ n, (List.range (4 * n)).map g =
    (List.range n).flatMap fun j => [g (4 * j), g (4 * j + 1), g (4 * j + 2), g (4 * j + 3)]
  | 0 => rfl
  | n + 1 => by
    rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, List.range_succ, List.range_succ,
      List.range_succ, List.range_succ, List.range_succ, List.flatMap_append, ← range_mul4 g n]
    simp

theorem vector_toList (x : Vector Word 16) : x.toList = (List.range 16).map fun j => x[j]! := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [Vector.getElem_toList, List.getElem_map, List.getElem_range]
    simp at h₁
    simp [h₁]

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
      flatMap_congr' fun x hx => h x (by simp [hx])]

/-- The 64 bytes at `p`, if the little-endian word at `p + 4j` is `x[j]`. -/
theorem bytesAt_eq_serialize (m : Mem) (p : Addr) (x : Vector Word 16)
    (h : ∀ j (hj : j < 16), m.readW (p + BitVec.ofNat 64 (4 * j)) 32 = x[j]) :
    bytesAt m p 64 = serialize x := by
  rw [serialize, bytesAt, show List.range 64 = List.range (4 * 16) from rfl, range_mul4,
    vector_toList, List.flatMap_map]
  refine flatMap_congr' fun j hj => ?_
  have hj' : j < 16 := List.mem_range.mp hj
  have e : ∀ i < 4, m (p + BitVec.ofNat 64 (4 * j + i)) = x[j].extractLsb' (8 * i) 8 := by
    intro i hi
    rw [← h j hj', show p + BitVec.ofNat 64 (4 * j + i) = p + BitVec.ofNat 64 (4 * j) +
      BitVec.ofNat 64 i by rw [BitVec.add_assoc, BitVec.ofNat_add]]
    exact Mem.readW_byte _ _ hi
  simp only [getElem!_pos x j hj']
  rw [← e 1 (by omega), ← e 2 (by omega), ← e 3 (by omega), ← e 0 (by omega)]
  rfl

end VG.Proof.Scrypt
