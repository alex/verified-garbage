import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.X25519.Arm.Limbs
import VerifiedGarbage.Impl.Ed25519.Arm.Scalar

/-! Radix-65536 arithmetic for subgroup-order reduction. -/
namespace VG.Proof.Ed25519.Arm
open VG.Proof.X25519.Arm VG.Spec.Ed25519 VG.Impl.Ed25519.Arm

theorem scalarComplement_lt (k : Nat) : scalarComplement k < 65536 := by
  unfold scalarComplement; omega

theorem scalarComplement_val : val16 scalarComplement 16 + L + 1 = 2 ^ 256 := by decide

theorem scalarDouble_val {f : Nat → Nat} {bit : Nat}
    (hf : val16 f 16 < L) (hb : bit < 2) :
    val16 (out (fun k => 2 * f k) bit) 16 = 2 * val16 f 16 + bit := by
  have h := chain_val (fun k => 2 * f k) bit 16
  rw [val16_cmul] at h
  have bound := order_bound
  have hc : chain (fun k => 2 * f k) bit 16 = 0 := by
    rcases Nat.eq_zero_or_pos (chain (fun k => 2 * f k) bit 16) with hz | hp
    · exact hz
    · have := Nat.le_mul_of_pos_right (2 ^ 256) hp
      change _ + 2 ^ 256 * _ = _ at h
      omega
  rw [hc, Nat.mul_zero, Nat.add_zero] at h
  exact h

theorem scalarSubtract_facts {f : Nat → Nat} (hf : val16 f 16 < 2 * L) :
    chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 ∧
    val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
      (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 % L := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := scalarComplement_val
  have hL := order_pos
  have hB := order_bound
  have hout := val16_lt (f := out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  have hcarry : chain (fun k => f k + scalarComplement k) 1 16 ≤ 1 := by
    have : 2 ^ 256 * chain (fun k => f k + scalarComplement k) 1 16 < 2 ^ 256 * 2 := by omega
    exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left this)
  refine ⟨hcarry, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcarry with hz | ho
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 = val16 f 16 :=
      val16_congr fun _ _ => by rw [hz]; rfl
    rw [he, Nat.mod_eq_of_lt (by rw [hz] at hv; omega)]
  · have he : val16 (fun k => sel (chain (fun j => f j + scalarComplement j) 1 16)
        (f k) (out (fun j => f j + scalarComplement j) 1 k)) 16 =
        val16 (out (fun j => f j + scalarComplement j) 1) 16 :=
      val16_congr fun _ _ => by rw [ho]; rfl
    rw [he]
    have heq : val16 f 16 = val16 (out (fun j => f j + scalarComplement j) 1) 16 + L := by
      rw [ho] at hv; omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem scalarCompare_carry {f : Nat → Nat} (hf : val16 f 16 < 2 ^ 256) :
    chain (fun k => f k + scalarComplement k) 1 16 = if val16 f 16 < L then 0 else 1 := by
  have hv := chain_val (fun k => f k + scalarComplement k) 1 16
  rw [val16_add] at hv
  have hc := scalarComplement_val
  have hl := order_pos
  have hout := val16_lt (f := out (fun k => f k + scalarComplement k) 1) (n := 16)
    fun _ _ => out_lt _ _ _
  split <;> omega

/-- Consume the low n bits of a word, in descending order. -/
def scalarConsumeBits (v n r : Nat) : Nat :=
  (List.range n).reverse.foldl (fun a j => (2 * a + v / 2 ^ j % 2) % L) r

theorem scalarConsumeBits_succ (v n r : Nat) :
    scalarConsumeBits v (n + 1) r = scalarConsumeBits v n ((2 * r + v / 2 ^ n % 2) % L) := by
  simp only [scalarConsumeBits, List.range_succ, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem scalarConsumeBits_eq (v n r : Nat) (hr : r < L) :
    scalarConsumeBits v n r = (2 ^ n * r + v % 2 ^ n) % L := by
  induction n generalizing r with
  | zero => simp only [scalarConsumeBits, List.range_zero, List.reverse_nil, List.foldl_nil,
      Nat.pow_zero, Nat.one_mul, Nat.mod_one, Nat.add_zero, Nat.mod_eq_of_lt hr]
  | succ n ih =>
    rw [scalarConsumeBits_succ, ih _ (Nat.mod_lt _ order_pos)]
    have hmod (a x z : Nat) : (a * (x % L) + z) % L = (a * x + z) % L := by
      rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
    rw [hmod, Nat.pow_succ, Nat.mod_mul]
    simp only [Nat.mul_add, Nat.mul_assoc]
    congr 1
    omega

end VG.Proof.Ed25519.Arm
