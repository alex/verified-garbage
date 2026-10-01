import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Phase

/-!
# X25519 on x86-64 with AVX512_IFMA: limbs as field elements

Untrusted: everything here is checked by Lean. Five limbs stand for an
element of `GF(p)` (`fe5`); the sums, differences (with the bias `2¹¹ p`),
carries and products of the stages are the field's operations on them.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG.Proof.X25519 VG.Spec.X25519

/-- The element of `GF(p)` five limbs stand for. -/
def fe5 (x : Nat → Nat) : Fe := toFe (lv x)

theorem lv_congr {x y : Nat → Nat} (h : ∀ i < 5, x i = y i) : lv x = lv y := by
  simp only [lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]

theorem fe5_congr {x y : Nat → Nat} (h : ∀ i < 5, x i = y i) : fe5 x = fe5 y := by
  rw [fe5, fe5, lv_congr h]

theorem fe5_add {x y z : Nat → Nat} (h : ∀ i < 5, z i = x i + y i) : fe5 z = fe5 x + fe5 y := by
  refine toFe_add (congrArg (· % P) ?_)
  simp only [lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
  omega

theorem lv_kbv : lv kbv = 2 ^ 11 * P := by decide

theorem fe5_sub {x y z : Nat → Nat} (h : ∀ i < 5, z i = x i + (kbv i - y i)) (hy : ∀ i < 5, y i ≤ kbv i) :
    fe5 z = fe5 x - fe5 y := by
  refine toFe_sub ?_
  have e : lv z + lv y = lv x + P * 2 ^ 11 := by
    rw [Nat.mul_comm, ← lv_kbv]
    have h0 := hy 0 (by decide); have h1 := hy 1 (by decide); have h2 := hy 2 (by decide)
    have h3 := hy 3 (by decide); have h4 := hy 4 (by decide)
    simp only [lv, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide)]
    simp only [kbv] at h0 h1 h2 h3 h4 ⊢
    omega
  rw [e, Nat.add_mul_mod_self_left]

theorem fe5_carry (x : Nat → Nat) (h4 : x 4 < 2 ^ 63) : fe5 (carryNat (2 ^ 51 - 1) 19 x) = fe5 x :=
  toFe_congr (carryNat_mod x h4)

theorem fe5_mul {a b : Nat → Nat} (ha : ∀ i < 5, a i < 2 ^ 52) (hb : ∀ i < 5, b i < 2 ^ 52) :
    fe5 (fun k => mulNat a b k) = fe5 a * fe5 b := by
  refine toFe_mul ?_
  rw [show (fun k => mulNat a b k) = mulNat a b from rfl, mulNat_mod,
    lv_congr (x := fun i => a i % 2 ^ 52) (y := a) (fun i hi => Nat.mod_eq_of_lt (ha i hi)),
    lv_congr (x := fun i => b i % 2 ^ 52) (y := b) (fun i hi => Nat.mod_eq_of_lt (hb i hi))]

theorem fe5_one : fe5 (fun i => if i = 0 then 1 else 0) = 1 := rfl

theorem fe5_a24 : fe5 (fun i => if i = 0 then 121665 else 0) = a24 := rfl

end VG.Proof.X25519.X86_64.Ifma
