import VerifiedGarbage.Proof.Ed25519.Bytes

/-! The primitive signing pipeline equals the complete RFC 8032 specification. -/
namespace VG.Proof.Ed25519
open VG VG.Spec.Ed25519

private theorem encodeLE_bytes (n x : Nat) : encodeLE n x = Proof.X25519.leBytes n x := by
  simp only [encodeLE, Proof.X25519.leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem decodeLE_encodeLE (n x : Nat) : decodeLE (encodeLE n x) = x % 256 ^ n := by
  rw [encodeLE_bytes, decodeLE_eq]
  induction n generalizing x with
  | zero => simp [Proof.X25519.leBytes, Proof.X25519.leNum, Nat.mod_one]
  | succ n ih =>
    rw [Proof.X25519.leBytes_succ, Proof.X25519.leNum, ih, BitVec.toNat_ofNat]
    change x % 256 + 256 * (x / 256 % 256 ^ n) = x % 256 ^ (n + 1)
    rw [Nat.pow_succ', Nat.mod_mul]

theorem decodeLE_scalarReduce (wide : List Byte) : decodeLE (scalarReduce wide) = decodeLE wide % L := by
  rw [scalarReduce, decodeLE_encodeLE, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide : 0 < L)) (by decide : L ≤ 256 ^ 32)

theorem prune_bound (expanded : List Byte) : prune expanded < 256 ^ 32 := by
  unfold prune
  change _ < 2 ^ 256
  exact Nat.or_lt_two_pow
    (Nat.lt_of_le_of_lt Nat.and_le_right (by decide : 2 ^ 254 - 8 < 2 ^ 256))
    (by decide)

theorem bytesAt_encodeLE (m : Mem) (p : Addr) (n : Nat) :
    bytesAt m p n = encodeLE n (decodeLE (bytesAt m p n)) := by
  rw [encodeLE_bytes, decodeLE_eq]
  change Spec.X25519.bytesAt m p n = Proof.X25519.leBytes n
    (Proof.X25519.leNum (Spec.X25519.bytesAt m p n))
  rw [Proof.X25519.leNum_bytesAt_read, Proof.X25519.bytesAt_leBytes]

/-- The cached key is constrained to the key derived from this very seed. -/
theorem sign_pipeline (seed pk message : List Byte) (hpk : pk = publicKey seed) :
    let expanded := Spec.Sha512.sha512 seed
    let scalar := encodeLE 32 (prune expanded)
    let nonce := scalarReduce (Spec.Sha512.sha512 (expanded.drop 32 ++ message))
    let r := scalarBase nonce
    let challenge := scalarReduce (Spec.Sha512.sha512 (r ++ pk ++ message))
    r ++ scalarMulAdd nonce challenge scalar = sign seed message := by
  dsimp only
  rw [scalarMulAdd, decodeLE_scalarReduce, decodeLE_scalarReduce, decodeLE_encodeLE,
    Nat.mod_eq_of_lt (prune_bound _), scalarBase, decodeLE_scalarReduce, hpk]
  rfl

end VG.Proof.Ed25519
