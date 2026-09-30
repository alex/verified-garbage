import VerifiedGarbage.Proof.Ed25519.Word64
import VerifiedGarbage.Proof.X25519.Field

/-! Target-independent facts for folding carries modulo 2^255 - 19. -/
namespace VG.Proof.Ed25519.Word64
open VG.Proof.X25519

/-- After adding a small word to a four-word number, folding a final
carry back as 38 cannot overflow the low word. -/
theorem foldCarry_low (r0 r1 r2 r3 : Word) (c : Bool) {a v : Nat}
    (ha : a < 2 ^ 256) (hv : v < 2 ^ 58)
    (h : val4 r0 r1 r2 r3 + 2 ^ 256 * c.toNat = a + v) :
    (r0 + BitVec.ofNat 64 (38 * c.toNat)).toNat = r0.toNat + 38 * c.toNat := by
  have hl := low_le_val4 r0 r1 r2 r3
  cases c with
  | false =>
    change (r0 + 0).toNat = r0.toNat + 0
    exact congrArg BitVec.toNat (BitVec.add_zero r0)
  | true =>
    have hb : r0.toNat + 38 < 2 ^ 64 := by
      simp only [Bool.toNat_true, Nat.mul_one] at h
      omega
    change (r0 + 38).toNat = r0.toNat + 38
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt hb

theorem foldCarry_field (r0 r1 r2 r3 : Word) (c : Bool) {a v : Nat}
    (ha : a < 2 ^ 256) (hv : v < 2 ^ 58)
    (h : val4 r0 r1 r2 r3 + 2 ^ 256 * c.toNat = a + v) :
    toFe (val4 (r0 + BitVec.ofNat 64 (38 * c.toNat)) r1 r2 r3) = toFe (a + v) := by
  have hn : val4 (r0 + BitVec.ofNat 64 (38 * c.toNat)) r1 r2 r3 =
      val4 r0 r1 r2 r3 + 38 * c.toNat := by
    simp only [val4]
    rw [foldCarry_low r0 r1 r2 r3 c ha hv h]
    omega
  apply toFe_congr
  rw [hn, ← h]
  exact (fold256 _ _).symm

end VG.Proof.Ed25519.Word64
