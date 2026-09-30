import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.Proof.X448.Ladder
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# X448: byte encodings

Untrusted: everything here is checked by Lean. The target-independent
little-endian helpers are shared with X25519; the width and clamping
lemmas here are specific to X448.
-/

namespace VG.Proof.X448

open VG.Spec.X448

open VG.Proof.X25519 (leNum leBytes)

theorem bytesAt_add (m : Mem) (p : Addr) (a b : Nat) :
    bytesAt m p (a + b) = bytesAt m p a ++ bytesAt m (p + BitVec.ofNat 64 a) b :=
  VG.Proof.X25519.bytesAt_add m p a b

theorem length_bytesAt (m : Mem) (p : Addr) (n : Nat) : (bytesAt m p n).length = n := by
  simp only [bytesAt, List.length_map, List.length_range]

theorem leNum_bytesAt_read (m : Mem) (p : Addr) (n : Nat) :
    leNum (bytesAt m p n) = (m.read p n).toNat := VG.Proof.X25519.leNum_bytesAt_read m p n

theorem decodeLittleEndian_eq (l : List Byte) : decodeLittleEndian l = leNum (l.take 56) := by
  suffices h : ∀ n, ((List.range n).map fun i => (l.getD i 0).toNat <<< (8 * i)).sum =
      leNum (l.take n) from h 56
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, VG.Proof.X25519.leNum_take_succ]
    simp only [Nat.shiftLeft_eq, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.mul_comm 8, Nat.pow_mul]
    congr 1
    rw [Nat.mul_comm, ← Nat.pow_mul, Nat.mul_comm n, Nat.pow_mul]

/-- `encodeUCoordinate` is the 56 bytes of the value. -/
theorem encodeUCoordinate_eq (x : Fe) : encodeUCoordinate x = leBytes 56 x.val := by
  simp only [encodeUCoordinate, leBytes, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem take_56 {l : List Byte} (h : l.length = 56) : l.take 56 = l :=
  List.take_of_length_le (by omega)

/-- X448 uses all 448 bits of the coordinate. -/
theorem decodeUCoordinate_eq {l : List Byte} (h : l.length = 56) :
    decodeUCoordinate l = leNum l := by
  rw [decodeUCoordinate, decodeLittleEndian_eq, take_56 h]

/-- The low two bits of the scalar are cleared. -/
theorem bit_and_252 : ∀ x < 256, ∀ r < 8,
    ((x &&& 252) >>> r) &&& 1 = if r < 2 then 0 else (x >>> r) &&& 1 := by decide +kernel

/-- Bit 447 is set, with the other bits in the last byte preserved. -/
theorem bit_or_128 : ∀ x < 256, ∀ r < 8,
    ((x ||| 128) >>> r) &&& 1 = if r = 7 then 1 else (x >>> r) &&& 1 := by decide +kernel

/-- The bits `0, …, 447` of the decoded scalar: those of its bytes, but for the
clamped ones (bits 0–1 are 0, bit 447 is 1). -/
theorem scalar_bit {kb : List Byte} (h : kb.length = 56) {t : Nat} (ht : t < 448) :
    bit (decodeScalar448 kb) t =
      if t < 2 then 0 else if t = 447 then 1 else ((kb.getD (t / 8) 0).toNat >>> (t % 8)) &&& 1 := by
  simp only [decodeScalar448, bit, decodeLittleEndian_eq]
  rw [List.take_of_length_le (by simp [h]), VG.Proof.X25519.leNum_bit,
    VG.Proof.X25519.getD_set _ _ _ (by simp [h]), VG.Proof.X25519.getD_set _ _ _ (by simp [h]), VG.Proof.X25519.getD_set _ _ _ (by simp [h])]
  rcases Nat.lt_or_ge t 8 with h8 | h8
  · rw [show t / 8 = 0 by omega, show t % 8 = t by omega]
    simp (disch := omega) only [ite_true, ite_eq_left, ite_eq_right]
    rw [BitVec.toNat_and, show (252 : BitVec 8).toNat = 252 from rfl,
      bit_and_252 _ (kb.getD 0 0).isLt _ h8]
  · by_cases h55 : t / 8 = 55
    · rw [h55]
      simp (disch := omega) only [ite_true, ite_eq_right]
      rw [BitVec.toNat_or, show (128 : BitVec 8).toNat = 128 from rfl, bit_or_128 _ (kb.getD 55 0).isLt _ (by omega)]
      split_ifs <;> omega
    · simp (disch := omega) only [ite_eq_left, ite_eq_right]


end VG.Proof.X448
