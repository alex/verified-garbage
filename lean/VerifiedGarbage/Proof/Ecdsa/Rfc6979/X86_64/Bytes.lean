import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Spec.Ecdsa.Rfc6979.P256Sha256

/-!
# Deterministic ECDSA on x86-64: big-endian numbers

The 32 bytes at an address, big-endian, from the byte reversals of their
four words (`ofBytes_32`); a number's encoding is determined by its value
(`toBytes_ofBytes`); and RFC 6979's conversions at P-256 (`bits2octets_eq`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Proof.Weierstrass.X86_64

/-- The bytes at an address, whichever specification names them. -/
theorem ecdsa_bytesAt : Spec.Ecdsa.bytesAt = Spec.Sha256.bytesAt := rfl

theorem ofBytes_32 (m : Mem) (q : Addr) :
    Spec.Weierstrass.ofBytes (Spec.Sha256.bytesAt m q 32) =
      (bswap64 (m.readW q 64)).toNat * 2 ^ 192 +
        (bswap64 (m.readW (q + BitVec.ofNat 64 8) 64)).toNat * 2 ^ 128 +
        (bswap64 (m.readW (q + BitVec.ofNat 64 16) 64)).toNat * 2 ^ 64 +
        (bswap64 (m.readW (q + BitVec.ofNat 64 24) 64)).toNat := by
  rw [bswap64_ofBytes, bswap64_ofBytes, bswap64_ofBytes, bswap64_ofBytes, ← ecdsa_bytesAt,
    show 32 = 8 + (8 + (8 + 8)) from rfl, bytesAt_add, bytesAt_add, bytesAt_add,
    ofBytes_append, ofBytes_append, ofBytes_append, length_bytesAt, List.length_append, length_bytesAt,
    List.length_append, length_bytesAt, length_bytesAt, Offset.add_add, Offset.add_add]
  simp only [Nat.reduceAdd, Nat.reducePow]
  omega

theorem toBytes_succ (len x : Nat) :
    Spec.Weierstrass.toBytes (len + 1) x = BitVec.ofNat 8 (x >>> (8 * len)) :: Spec.Weierstrass.toBytes len x := by
  simp only [Spec.Weierstrass.toBytes, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.map_cons]

theorem toBytes_add (len a y : Nat) :
    Spec.Weierstrass.toBytes len (a * 2 ^ (8 * len) + y) = Spec.Weierstrass.toBytes len y := by
  simp only [Spec.Weierstrass.toBytes]
  refine List.map_congr_left fun i hi => ?_
  have hi : i < len := by simpa using hi
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have e : a * 2 ^ (8 * len) = (a * 2 ^ (8 * (len - i - 1)) * 2 ^ 8) * 2 ^ (8 * i) := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_mul_mod_self_right]

theorem ofBytes_single (b : Byte) : Spec.Weierstrass.ofBytes [b] = b.toNat := by
  simp [Spec.Weierstrass.ofBytes]

theorem pow256 (n : Nat) : (256 : Nat) ^ n = 2 ^ (8 * n) := by
  rw [Nat.pow_mul]

theorem ofBytes_lt : ∀ l : List Byte, Spec.Weierstrass.ofBytes l < 2 ^ (8 * l.length)
  | [] => by decide
  | b :: l => by
    have := ofBytes_lt l
    have hb := b.isLt
    rw [show b :: l = [b] ++ l from rfl, ofBytes_append, ofBytes_single, pow256,
      List.length_append, List.length_singleton, Nat.mul_add, Nat.pow_add, Nat.mul_one]
    have : b.toNat * 2 ^ (8 * l.length) + 2 ^ (8 * l.length) ≤ 2 ^ 8 * 2 ^ (8 * l.length) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
    omega

theorem toBytes_ofBytes : ∀ (l : List Byte), Spec.Weierstrass.toBytes l.length (Spec.Weierstrass.ofBytes l) = l
  | [] => rfl
  | b :: l => by
    have hl := ofBytes_lt l
    have hb := b.isLt
    rw [show b :: l = [b] ++ l from rfl, ofBytes_append, ofBytes_single, pow256,
      List.length_append, List.length_singleton, Nat.add_comm 1, toBytes_succ, toBytes_add, toBytes_ofBytes l]
    refine congrArg (· :: l) ?_
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
      Nat.div_eq_of_lt hl, Nat.zero_add, Nat.mod_eq_of_lt hb]

/-! ## At P-256 -/

theorem nBits_p256 : Spec.Ecdsa.nBits Spec.P256.curve = 256 := by
  have h₁ : 255 ≤ Spec.P256.curve.n.log2 := (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h₂ : Spec.P256.curve.n.log2 < 256 := (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  show Spec.P256.curve.n.log2 + 1 = 256
  omega

theorem hashToInt_32 {h : List Byte} (hl : h.length = 32) :
    Spec.Ecdsa.hashToInt Spec.P256.curve h = Spec.Weierstrass.ofBytes h := by
  rw [Spec.Ecdsa.hashToInt, nBits_p256, hl]; rfl

theorem rlen_p256 : Spec.Ecdsa.Rfc6979.rlen Spec.P256.curve = 32 := by
  rw [Spec.Ecdsa.Rfc6979.rlen, nBits_p256]

theorem bits2octets_eq {h : List Byte} (hl : h.length = 32) :
    Spec.Ecdsa.Rfc6979.bits2octets Spec.P256.curve h =
      Spec.Weierstrass.toBytes 32 (Spec.Weierstrass.ofBytes h % Spec.P256.n) := by
  rw [Spec.Ecdsa.Rfc6979.bits2octets, Spec.Ecdsa.Rfc6979.int2octets, Spec.Ecdsa.Rfc6979.bits2int, rlen_p256,
    hashToInt_32 hl]; rfl

end VG.Proof.Ecdsa.Rfc6979.X86_64
