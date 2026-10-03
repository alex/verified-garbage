import VerifiedGarbage.Proof.Ed25519.X86.ScalarLoop
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Spec.Ed25519.Contract

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86 VG.Impl.Ed25519.X86
open VG.Proof.X25519 (leNum leBytes)

theorem encodeLE_eq (n x : Nat) : Spec.Ed25519.encodeLE n x = leBytes n x := by
  unfold Spec.Ed25519.encodeLE leBytes
  congr 1
  funext i
  rw [Nat.shiftRight_eq_div_pow, show 256 ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]

theorem addr_offset {x : BitVec 32} {o d : Nat} (hx : x.toNat + o + d < 2 ^ 32) :
    addr x (o + d) = addr x o + BitVec.ofNat 64 d := by
  rw [addr_eq (by omega_using [hx]), addr_eq (by omega_using [hx]), BitVec.add_assoc,
    BitVec.ofNat_add_ofNat]

/-- Little-endian decoding of any number of scratch words. -/
theorem decode_words {x : BitVec 32} {o : Nat} (m : Mem) : ∀ n,
    x.toNat + o + 4 * n ≤ 2 ^ 32 →
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m (addr x o) (4 * n)) =
      num (fun k => wv m x (o + 4 * k)) n
  | 0, _ => rfl
  | n + 1, hx => by
    rw [show 4 * (n + 1) = 4 * n + 4 by omega_using []]
    rw [decodeLE_eq]
    change leNum (Spec.X25519.bytesAt m (addr x o) (4 * n + 4)) = _
    rw [Proof.X25519.bytesAt_add, Proof.X25519.leNum_append, Proof.X25519.length_bytesAt,
      Proof.X25519.leNum_bytesAt_32bit]
    have hn := decode_words (x := x) (o := o) m n (by omega_using [hx])
    rw [decodeLE_eq] at hn
    change leNum (Spec.X25519.bytesAt m (addr x o) (4 * n)) = _ at hn
    rw [hn, num_succ, ← addr_offset (by omega_using [hx])]
    have hp : 256 ^ (4 * n) = (2 ^ 32) ^ n := by
      rw [Nat.pow_mul]
    rw [hp]

theorem scalarInput_bytes {x : BitVec 32} (m : Mem) (hx : x.toNat + 8192 ≤ 2 ^ 32) :
    scalarInput m x = Spec.Ed25519.bytesAt m (addr x 128) 64 := by
  apply List.map_congr_left
  intro i hi
  have hi' : i < 64 := List.mem_range.mp hi
  rw [addr_offset (by omega_using [hx, hi'])]

theorem scalarInput_num {x : BitVec 32} (m : Mem) (hx : x.toNat + 8192 ≤ 2 ^ 32) :
    Spec.Ed25519.decodeLE (scalarInput m x) = num (fun k => wv m x (128 + 4 * k)) 16 := by
  rw [scalarInput_bytes m hx]
  exact decode_words m 16 (by omega_using [hx])

theorem num_shift (f : Nat → Nat) (n : Nat) : num f (n + 1) = f 0 + 2 ^ 32 * num (fun k => f (k + 1)) n := by
  induction n with
  | zero => simp [num]
  | succ n ih =>
    rw [num_succ, ih, num_succ, Nat.mul_add, Nat.pow_succ (2 ^ 32) n, Nat.mul_comm ((2 ^ 32) ^ n) (2 ^ 32),
      Nat.mul_assoc]
    omega_using []

theorem num_digit : ∀ (j : Nat) {f : Nat → Nat} {n : Nat}, (∀ k < n, f k < 2 ^ 32) → j < n →
    num f n / (2 ^ 32) ^ j % 2 ^ 32 = f j
  | 0, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [num_shift, Nat.pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (h 0 hj)]
  | j + 1, f, n, h, hj => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega_using [hj]⟩
    rw [num_shift, Nat.pow_succ (2 ^ 32) j, Nat.mul_comm ((2 ^ 32) ^ j) (2 ^ 32), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt (h 0 (by omega_using [])), Nat.zero_add]
    exact num_digit j (fun k hk => h (k + 1) (by omega_using [hk])) (by omega_using [hj])
end VG.Proof.Ed25519.X86
