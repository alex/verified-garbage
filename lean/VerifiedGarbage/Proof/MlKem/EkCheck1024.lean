import VerifiedGarbage.Proof.MlKem.EkCheck

/-!
# ML-KEM-1024: the encapsulation key check, for every target

The modulus check of §7.2 for any parameter set, as `EkCheck.lean` states it
for ML-KEM-768: it holds exactly when both 12-bit fields of every 3-byte group
of `ek[0 : 384k]` are less than `q` (`ekCheck_iff`); for ML-KEM-1024, the 512
groups of the first 1536 bytes of a 1568-byte key (`ekCheck1024`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

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

/-- The encapsulation key check of ML-KEM-1024 (§7.2) of a key of 1568
bytes: both 12-bit fields of each of the 512 groups of 3 bytes of
`ek[0 : 1536]` are less than `q`. -/
theorem ekCheck1024 (ek : List Byte) (h : ek.length = 1568) :
    ekCheck mlKem1024 ek = true ↔ ∀ g < 512, field0 ek g < q ∧ field1 ek g < q :=
  ekCheck_iff mlKem1024 ek h

end VG.Proof.MlKem
