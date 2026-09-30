import VerifiedGarbage.Spec.MlDsa
import VerifiedGarbage.Proof.Sha3.Stream

/-!
# ML-DSA: `H` and `G` through the streaming sponge

Untrusted: everything here is checked by Lean. `H` and `G` (SHAKE256 and
SHAKE128) are the output of `squeezeFrom` from position 0 of the state that
padding the message leaves (`H_eq`, `G_eq`), which is what a caller of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze` computes; and
a shorter output is a prefix of a longer one (`H_take`, `G_take`), so a
bound larger than another draws the same first bytes.
-/

namespace VG.Proof.MlDsa.Sample

open VG.Spec.MlDsa
open VG.Spec.Sha3
open VG.Proof.Sha3 (length_squeeze squeeze_getElem)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`:
what `vg_keccak_pad` leaves. -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : State := absorb rate (pad rate suffix m)

theorem squeezeFrom_zero (rate : Nat) (S : State) (d : Nat) : squeezeFrom rate S 0 d = squeeze rate S d := by
  simp only [squeezeFrom, squeeze, Nat.zero_add, List.drop_zero]

/-- `H(s, d)`: rate 136, suffix `0x1f`. -/
theorem H_eq (s : List Byte) (d : Nat) : H s d = squeezeFrom 136 (padded 136 shakeSuffix s) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- `G(s, d)`: rate 168, suffix `0x1f`. -/
theorem G_eq (s : List Byte) (d : Nat) : G s d = squeezeFrom 168 (padded 168 shakeSuffix s) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- The first `d` bytes of a longer output. -/
theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [length_squeeze hr hr'] at h₂
  rw [List.getElem_take, squeeze_getElem hr hr' _ h₂, squeeze_getElem hr hr' _ (by omega)]

theorem H_length (s : List Byte) (d : Nat) : (H s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem G_length (s : List Byte) (d : Nat) : (G s d).length = d := length_squeeze (by decide) (by decide) _ _

theorem H_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (H s d').take d = H s d :=
  squeeze_take (by decide) (by decide) _ h

theorem G_take (s : List Byte) {d d' : Nat} (h : d ≤ d') : (G s d').take d = G s d :=
  squeeze_take (by decide) (by decide) _ h

end VG.Proof.MlDsa.Sample
