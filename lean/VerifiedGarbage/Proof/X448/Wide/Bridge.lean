import VerifiedGarbage.Proof.X448.Wide.Limbs
import VerifiedGarbage.Proof.X448.Limbs

/-! Untrusted: the exact-value bridge between the old and wide limb layouts. -/
namespace VG.Proof.X448.Wide

/-- Combine two neighboring 28-bit limbs. -/
def paired (f : Nat → Nat) (i : Nat) : Nat :=
  f (2 * i) + VG.Proof.X448.radix * f (2 * i + 1)

theorem radix_pair : VG.Proof.X448.radix ^ 2 = radix := by decide

theorem paired_val (f : Nat → Nat) (n : Nat) :
    valN (paired f) n = VG.Proof.X448.valN f (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      VG.Proof.X448.valN_succ, VG.Proof.X448.valN_succ, valN_succ, ih, paired,
      Nat.pow_succ, Nat.pow_mul, radix_pair]
    ring

theorem paired_bound {f : Nat → Nat} (h : ∀ i < 16, f i < VG.Proof.X448.radix) :
    ∀ i < 8, paired f i < radix := by
  intro i hi
  have h0 := h (2 * i) (by omega)
  have h1 := h (2 * i + 1) (by omega)
  simp only [paired, VG.Proof.X448.radix, radix] at *
  omega

/-- Split a normalized wide limb back into the existing field-slot layout. -/
def unpacked (f : Nat → Nat) (i : Nat) : Nat :=
  if i % 2 = 0 then f (i / 2) % VG.Proof.X448.radix else f (i / 2) / VG.Proof.X448.radix

theorem paired_unpacked (f : Nat → Nat) (i : Nat) : paired (unpacked f) i = f i := by
  simp only [paired, unpacked, show (2 * i) % 2 = 0 by omega,
    show (2 * i + 1) % 2 = 1 by omega, show (2 * i) / 2 = i by omega,
    show (2 * i + 1) / 2 = i by omega, ite_true, ite_false, Nat.one_ne_zero]
  exact Nat.mod_add_div _ _

theorem unpacked_val (f : Nat → Nat) :
    VG.Proof.X448.valN (unpacked f) 16 = valN f 8 := by
  rw [← paired_val (unpacked f) 8]
  exact valN_congr (fun i _ => paired_unpacked f i)

theorem unpacked_bound {f : Nat → Nat} (h : ∀ i < 8, f i < radix) :
    ∀ i < 16, unpacked f i < VG.Proof.X448.radix := by
  intro i hi
  have hf := h (i / 2) (by omega)
  simp only [unpacked]
  split
  · exact Nat.mod_lt _ (by decide)
  · simp only [radix] at hf
    simp only [VG.Proof.X448.radix]
    omega

end VG.Proof.X448.Wide
