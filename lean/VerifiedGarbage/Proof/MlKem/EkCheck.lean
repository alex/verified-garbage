import VerifiedGarbage.Proof.MlKem.Encode

/-!
# ML-KEM: the encapsulation key check, for every target

The modulus check of §7.2, `ByteEncode₁₂(ByteDecode₁₂(ek[0 : 384k])) = ek[0 :
384k]`, holds exactly when both 12-bit fields of every 3-byte group of `ek[0 :
384k]` are less than `q` (`encode12_decode12`, `ekCheck_iff`, for any parameter set,
and `ekCheck768`, `ekCheck1024`): what a constant-time implementation checks,
without encoding anything.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- The first 12-bit field of the 3-byte group `g` of `B`:
`B[3g] + 256 · (B[3g + 1] mod 16)`. -/
def field0 (B : List Byte) (g : Nat) : Nat :=
  (B.getD (3 * g) 0).toNat + 256 * ((B.getD (3 * g + 1) 0).toNat % 16)

/-- The second 12-bit field of the 3-byte group `g` of `B`:
`⌊B[3g + 1] / 16⌋ + 16 · B[3g + 2]`. -/
def field1 (B : List Byte) (g : Nat) : Nat :=
  (B.getD (3 * g + 1) 0).toNat / 16 + 16 * (B.getD (3 * g + 2) 0).toNat

/-! ## Lists -/

theorem flatMap_range_inj {α : Type} {g₁ g₂ : Nat → List α} {c N : Nat} (hc : 0 < c)
    (h₁ : ∀ i < N, (g₁ i).length = c) (h₂ : ∀ i < N, (g₂ i).length = c) :
    (List.range N).flatMap g₁ = (List.range N).flatMap g₂ ↔ ∀ i < N, g₁ i = g₂ i := by
  constructor
  · intro h i hi
    refine List.ext_getElem? fun j => ?_
    by_cases hj : j < c
    · have := congrArg (·[c * i + j]?) h
      simp only [getElem?_flatMap_const _ hc _ fun a ha => h₁ a (List.mem_range.mp ha),
        getElem?_flatMap_const _ hc _ fun a ha => h₂ a (List.mem_range.mp ha),
        show (c * i + j) / c = i by rw [Nat.mul_add_div hc, Nat.div_eq_of_lt hj, Nat.add_zero],
        show (c * i + j) % c = j by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj],
        List.getElem?_range hi, Option.bind_some] at this
      exact this
    · rw [List.getElem?_eq_none (by rw [h₁ i hi]; omega), List.getElem?_eq_none (by rw [h₂ i hi]; omega)]
  · intro h
    simp only [List.flatMap_def]
    exact congrArg List.flatten (List.map_congr_left fun i hi => h i (List.mem_range.mp hi))

theorem getD_take_of_lt {α : Type} (L : List α) {x : α} {c j : Nat} (hj : j < c) :
    (L.take c).getD j x = L.getD j x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj]

theorem slice_getD {α : Type} (L : List α) (x : α) {s c j : Nat} (hj : j < c) :
    ((L.drop s).take c).getD j x = L.getD (s + j) x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hj, List.getElem?_drop]

/-- A list is the concatenation of its groups of `c`. -/
theorem eq_flatMap_slices {α : Type} [Inhabited α] (L : List α) {c N : Nat} (hc : 0 < c)
    (hL : L.length = c * N) : L = (List.range N).flatMap fun i => (L.drop (c * i)).take c := by
  have hl : ∀ i < N, ((L.drop (c * i)).take c).length = c := fun i hi => by
    have : c * i + c ≤ c * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
    simp only [List.length_take, List.length_drop, hL]
    omega
  refine eq_flatMap hc hl hL fun i hi j hj => ?_
  have : c * i + c ≤ c * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
  rw [getElem!_pos L _ (by omega), getElem!_pos _ _ (by rw [hl i hi]; exact hj), List.getElem_take,
    List.getElem_drop]

/-! ## One polynomial -/

theorem bytes3_eq (L : List Byte) (hL : L.length = 384) :
    L = (List.range 128).flatMap fun g => [L.getD (3 * g) 0, L.getD (3 * g + 1) 0, L.getD (3 * g + 2) 0] :=
  eq_flatMap (c := 3) (by decide) (fun _ _ => rfl) hL fun i hi j hj => by
    rw [getElem!_pos L _ (by omega)]
    have e : ∀ k (hk : k < L.length), L[k] = L.getD k 0 := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact e (3 * i) (by omega)
    · exact e (3 * i + 1) (by omega)
    · exact e (3 * i + 2) (by omega)

private theorem ofNat8_eq_iff (x : Nat) (b : Byte) : BitVec.ofNat 8 x = b ↔ x % 256 = b.toNat := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat]

/-- The three bytes of two 12-bit fields determine them. -/
private theorem bytes3_inj {a b a' b' : Nat} (ha : a < 4096) (hb : b < 4096) (ha' : a' < 4096)
    (hb' : b' < 4096) :
    (a % 256 = a' % 256 ∧ (a / 256 + 16 * (b % 16)) % 256 = (a' / 256 + 16 * (b' % 16)) % 256 ∧
      b / 16 % 256 = b' / 16 % 256) ↔ (a = a' ∧ b = b') := by
  omega

/-- The encoding of the two fields reduced modulo `q` is the encoding of
the fields exactly when they are less than `q`. -/
private theorem group_ok {F₀ F₁ c₀ c₁ c₂ : Nat} (h₀ : F₀ < 4096) (h₁ : F₁ < 4096) (e₀ : c₀ = F₀ % 256)
    (e₁ : c₁ = (F₀ / 256 + 16 * (F₁ % 16)) % 256) (e₂ : c₂ = F₁ / 16 % 256) :
    (F₀ % 3329 % 256 = c₀ ∧ (F₀ % 3329 / 256 + 16 * (F₁ % 3329 % 16)) % 256 = c₁ ∧
      F₁ % 3329 / 16 % 256 = c₂) ↔ (F₀ < 3329 ∧ F₁ < 3329) := by
  subst e₀ e₁ e₂
  have := Nat.mod_lt F₀ (show 3329 > 0 by decide)
  have := Nat.mod_lt F₁ (show 3329 > 0 by decide)
  rw [bytes3_inj (by omega) (by omega) h₀ h₁, Nat.mod_eq_iff_lt (by decide),
    Nat.mod_eq_iff_lt (by decide)]

/-- `ByteEncode₁₂(ByteDecode₁₂(C)) = C` exactly when both 12-bit fields of
every 3-byte group of `C` are less than `q`. -/
theorem encode12_decode12 (C : List Byte) (hC : C.length = 384) :
    encode12 (decode12 C) = C ↔ ∀ g < 128, field0 C g < q ∧ field1 C g < q := by
  conv => lhs; rhs; rw [bytes3_eq C hC]
  rw [encode12_eq, flatMap_range_inj (c := 3) (by decide) (fun _ _ => rfl) (fun _ _ => rfl)]
  refine forall_congr' fun g => imp_congr_right fun hg => ?_
  rw [decode12_even C hC hg, decode12_odd C hC hg, val_ofNat, val_ofNat]
  simp only [List.cons.injEq, and_true, ofNat8_eq_iff, field0, field1, q_eq, Nat.mod_mod]
  have := byte_lt (C.getD (3 * g) 0); have := byte_lt (C.getD (3 * g + 1) 0)
  have := byte_lt (C.getD (3 * g + 2) 0)
  exact group_ok (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ## The encapsulation key check -/

/-- The encapsulation key check (§7.2) of a key of `384k + 32` bytes: both
12-bit fields of each of the `128k` groups of 3 bytes of `ek[0 : 384k]` are
less than `q`. -/
theorem ekCheck_iff (p : Params) (ek : List Byte) (h : ek.length = p.ekLen) :
    ekCheck p ek = true ↔ ∀ g < 128 * p.k, field0 ek g < q ∧ field1 ek g < q := by
  have hE : (ek.take (384 * p.k)).length = 384 * p.k := by
    simp only [List.length_take, h, Params.ekLen]; omega
  have hs : ∀ i < p.k, (((ek.take (384 * p.k)).drop (384 * i)).take 384).length = 384 := fun i hi => by
    simp only [List.length_take, List.length_drop, hE]; omega
  simp only [ekCheck, h, Bool.and_eq_true, beq_iff_eq, decide_true, true_and]
  rw [encodeVec, decodeVec, List.flatMap_map]
  conv => lhs; rhs; rw [eq_flatMap_slices (ek.take (384 * p.k)) (c := 384) (N := p.k) (by decide) hE]
  rw [flatMap_range_inj (c := 384) (by decide) (fun _ _ => encode12_length _) hs]
  constructor
  · intro H g hg
    have := (encode12_decode12 _ (hs (g / 128) (by omega))).mp (H (g / 128) (by omega)) (g % 128)
      (by omega)
    simp only [field0, field1, slice_getD _ _ (show 3 * (g % 128) < 384 by omega),
      slice_getD _ _ (show 3 * (g % 128) + 1 < 384 by omega),
      slice_getD _ _ (show 3 * (g % 128) + 2 < 384 by omega)] at this
    simp only [field0, field1]
    rw [getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega)] at this
    rwa [show 384 * (g / 128) + 3 * (g % 128) = 3 * g by omega,
      show 384 * (g / 128) + (3 * (g % 128) + 1) = 3 * g + 1 by omega,
      show 384 * (g / 128) + (3 * (g % 128) + 2) = 3 * g + 2 by omega] at this
  · intro H i hi
    refine (encode12_decode12 _ (hs i hi)).mpr fun g hg => ?_
    have := H (128 * i + g) (by omega)
    simp only [field0, field1, slice_getD _ _ (show 3 * g < 384 by omega),
      slice_getD _ _ (show 3 * g + 1 < 384 by omega), slice_getD _ _ (show 3 * g + 2 < 384 by omega)]
    rw [getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega), getD_take_of_lt _ (by omega),
      show 384 * i + 3 * g = 3 * (128 * i + g) by omega,
      show 384 * i + (3 * g + 1) = 3 * (128 * i + g) + 1 by omega,
      show 384 * i + (3 * g + 2) = 3 * (128 * i + g) + 2 by omega]
    exact this

/-- The encapsulation key check of ML-KEM-768 (§7.2) of a key of 1184
bytes: both 12-bit fields of each of the 384 groups of 3 bytes of
`ek[0 : 1152]` are less than `q`. -/
theorem ekCheck768 (ek : List Byte) (h : ek.length = 1184) :
    ekCheck mlKem768 ek = true ↔ ∀ g < 384, field0 ek g < q ∧ field1 ek g < q :=
  ekCheck_iff mlKem768 ek h

/-- The encapsulation key check of ML-KEM-1024 (§7.2) of a key of 1568
bytes: both 12-bit fields of each of the 512 groups of 3 bytes of
`ek[0 : 1536]` are less than `q`. -/
theorem ekCheck1024 (ek : List Byte) (h : ek.length = 1568) :
    ekCheck mlKem1024 ek = true ↔ ∀ g < 512, field0 ek g < q ∧ field1 ek g < q :=
  ekCheck_iff mlKem1024 ek h

end VG.Proof.MlKem
