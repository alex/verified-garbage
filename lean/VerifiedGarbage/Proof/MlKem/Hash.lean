import VerifiedGarbage.Proof.Sha3.SqueezeFrom
import VerifiedGarbage.Spec.Sha3.Contract
import VerifiedGarbage.Spec.MlKem

/-!
# ML-KEM: the hash functions and XOFs through the streaming sponge

Untrusted: everything here is checked by Lean. What a caller of
`vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze`
(`Spec/Sha3/Contract.lean`) needs to conclude that it computed `H`, `J`,
`G`, `PRF` or `XOF` (§4.1): from the all-zero state, which represents the
empty message (`repr_nil`), absorbing the pieces of the message, padding
with the suffix of the function (`sha3Suffix32`, `shakeSuffix32`), and
squeezing from position 0 gives the function (`H_eq`, `J_eq`, `G_eq`,
`prf_eq`, `xof_eq`, as `squeezeFrom` of the padded state `padded`); and
output squeezed in pieces is the concatenation (`squeezeFrom_append`).
Byte `p` of the XOF output is the same whatever the length asked for
(`xof_getD`, `xofByte`).
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem
open VG.Spec.Sha3
open VG.Proof.Sha3 (Rep rep_nil byteOf iterF length_squeezeFrom squeezeFrom_getElem length_squeeze
  squeeze_getElem)

/-- The state after absorbing `m` padded with `suffix`, for the rate `rate`:
what `vg_keccak_pad` leaves (`padContract`). -/
abbrev padded (rate : Nat) (suffix : Byte) (m : List Byte) : State := absorb rate (pad rate suffix m)

/-- The all-zero state represents the empty message. -/
theorem repr_nil {mem : Mem} {p : Addr} {rate : Nat} (h : stateAt mem p = Spec.Sha3.zero) :
    Repr mem p rate [] := by
  show stateAt mem p = Rep rate []
  rw [rep_nil, h]

/-- The `suffix` argument of `vg_keccak_pad` for SHA-3. -/
theorem sha3Suffix32 : (0x06 : BitVec 32).setWidth 8 = sha3Suffix := by decide

/-- The `suffix` argument of `vg_keccak_pad` for SHAKE. -/
theorem shakeSuffix32 : (0x1f : BitVec 32).setWidth 8 = shakeSuffix := by decide

theorem rate72 : 72 ∈ rates := by decide
theorem rate136 : 136 ∈ rates := by decide
theorem rate168 : 168 ∈ rates := by decide

/-- Output from position 0 is the output of `squeeze`. -/
theorem squeezeFrom_zero (rate : Nat) (S : State) (d : Nat) : squeezeFrom rate S 0 d = squeeze rate S d := by
  simp only [squeezeFrom, squeeze, Nat.zero_add, List.drop_zero]

/-- Output squeezed in two pieces. -/
theorem squeezeFrom_append {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) (p a b : Nat) :
    squeezeFrom rate S p a ++ squeezeFrom rate S (p + a) b = squeezeFrom rate S p (a + b) := by
  refine List.ext_getElem (by rw [List.length_append, length_squeezeFrom hr hr', length_squeezeFrom hr hr',
    length_squeezeFrom hr hr']) fun i h₁ h₂ => ?_
  rw [length_squeezeFrom hr hr'] at h₂
  rw [squeezeFrom_getElem hr hr' _ h₂, List.getElem_append]
  split
  · rename_i h
    rw [length_squeezeFrom hr hr'] at h
    rw [squeezeFrom_getElem hr hr' _ h]
  · rename_i h
    rw [length_squeezeFrom hr hr'] at h
    rw [squeezeFrom_getElem hr hr' _ (by rw [length_squeezeFrom hr hr']; omega),
      show p + a + (i - (squeezeFrom rate S p a).length) = p + i by
        rw [length_squeezeFrom hr hr']; omega]

/-- The first `d` bytes of a longer output. -/
theorem squeeze_take {rate : Nat} (hr : 0 < rate) (hr' : rate ≤ 200) (S : State) {d d' : Nat}
    (h : d ≤ d') : (squeeze rate S d').take d = squeeze rate S d := by
  refine List.ext_getElem (by simp [length_squeeze hr hr']; omega) fun i h₁ h₂ => ?_
  rw [length_squeeze hr hr'] at h₂
  rw [List.getElem_take, squeeze_getElem hr hr' _ h₂, squeeze_getElem hr hr' _ (by omega)]

/-! ## The functions of §4.1 -/

theorem sha3_256_eq (m : List Byte) : sha3_256 m = squeezeFrom 136 (padded 136 sha3Suffix m) 0 32 := by
  rw [squeezeFrom_zero]; rfl

theorem sha3_512_eq (m : List Byte) : sha3_512 m = squeezeFrom 72 (padded 72 sha3Suffix m) 0 64 := by
  rw [squeezeFrom_zero]; rfl

theorem shake128_eq (m : List Byte) (d : Nat) :
    shake128 m d = squeezeFrom 168 (padded 168 shakeSuffix m) 0 d := by
  rw [squeezeFrom_zero]; rfl

theorem shake256_eq (m : List Byte) (d : Nat) :
    shake256 m d = squeezeFrom 136 (padded 136 shakeSuffix m) 0 d := by
  rw [squeezeFrom_zero]; rfl

/-- `H(s) = SHA3-256(s)`: rate 136, suffix `0x06`, 32 bytes. -/
theorem H_eq (s : List Byte) : H s = squeezeFrom 136 (padded 136 sha3Suffix s) 0 32 := sha3_256_eq s

/-- `J(s) = SHAKE256(s, 256)`: rate 136, suffix `0x1f`, 32 bytes. -/
theorem J_eq (s : List Byte) : J s = squeezeFrom 136 (padded 136 shakeSuffix s) 0 32 := shake256_eq s 32

/-- `G(c) = SHA3-512(c)`, as its halves: rate 72, suffix `0x06`, 32 bytes
from position 0 and 32 bytes from position 32. -/
theorem G_eq (c : List Byte) :
    G c = (squeezeFrom 72 (padded 72 sha3Suffix c) 0 32, squeezeFrom 72 (padded 72 sha3Suffix c) 32 32) := by
  have e := squeezeFrom_append (rate := 72) (by decide) (by decide) (padded 72 sha3Suffix c) 0 32 32
  have hl := length_squeezeFrom (rate := 72) (by decide) (by decide) (padded 72 sha3Suffix c) 0 32
  simp only [G, sha3_512_eq, ← e, List.take_left' hl, List.drop_left' hl]

/-- `PRF_η(s, b) = SHAKE256(s ‖ b, 8 · 64η)`: rate 136, suffix `0x1f`,
`64η` bytes. -/
theorem prf_eq (η : Nat) (s : List Byte) (b : Byte) :
    prf η s b = squeezeFrom 136 (padded 136 shakeSuffix (s ++ [b])) 0 (64 * η) := shake256_eq _ _

/-- `XOF` (SHAKE128): rate 168, suffix `0x1f`. -/
theorem xof_eq (B : List Byte) (ℓ : Nat) : xof B ℓ = squeezeFrom 168 (padded 168 shakeSuffix B) 0 ℓ :=
  shake128_eq B ℓ

theorem H_length (s : List Byte) : (H s).length = 32 := length_squeeze (by decide) (by decide) _ _

theorem J_length (s : List Byte) : (J s).length = 32 := length_squeeze (by decide) (by decide) _ _

theorem G_fst_length (c : List Byte) : (G c).1.length = 32 := by
  simp only [G, List.length_take]
  rw [show (sha3_512 c).length = 64 from length_squeeze (by decide) (by decide) _ _]
  rfl

theorem G_snd_length (c : List Byte) : (G c).2.length = 32 := by
  simp only [G, List.length_drop]
  rw [show (sha3_512 c).length = 64 from length_squeeze (by decide) (by decide) _ _]

theorem prf_length (η : Nat) (s : List Byte) (b : Byte) : (prf η s b).length = 64 * η :=
  length_squeeze (by decide) (by decide) _ _

/-- Byte `p` of the output of `XOF` after absorbing `B`: byte `p mod 168`
of the padded state after `⌊p / 168⌋` more permutations. -/
def xofByte (B : List Byte) (p : Nat) : Byte :=
  byteOf (iterF (p / 168) (padded 168 shakeSuffix B)) (p % 168)

theorem xof_length (B : List Byte) (ℓ : Nat) : (xof B ℓ).length = ℓ :=
  length_squeeze (by decide) (by decide) _ _

theorem xof_getD (B : List Byte) {ℓ p : Nat} (hp : p < ℓ) : (xof B ℓ).getD p 0 = xofByte B p := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [xof_length]; exact hp),
    Option.getD_some]
  exact squeeze_getElem (by decide) (by decide) _ hp

/-- Byte `i` of output squeezed from position `pos` of the XOF. -/
theorem xof_squeezeFrom_getElem (B : List Byte) {pos d i : Nat} (hi : i < d) :
    (squeezeFrom 168 (padded 168 shakeSuffix B) pos d)[i]'(by
      rw [length_squeezeFrom (by decide) (by decide)]; exact hi) = xofByte B (pos + i) :=
  squeezeFrom_getElem (by decide) (by decide) _ hi

end VG.Proof.MlKem
