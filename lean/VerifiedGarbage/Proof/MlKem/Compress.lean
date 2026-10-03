import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Spec.MlKem.Poly

/-!
# ML-KEM: Compress and Decompress without division, for every target

`Compress_d` (4.7) divides by `q`, and `Decompress_d` (4.8) by `2ᵈ`. For the
widths ML-KEM-768 uses (`compressWidths`: 1, 4 and 10), an implementation
computes them with a 32-bit multiply-low, an addition and shifts:

* `Compress_d(x) = ((x · M_d + 262080) >> 19) mod 2ᵈ` for every `x < q`,
  with `M₁ = 315`, `M₄ = 2520` and `M₁₀ = 161271` (`compressMul`); the
  intermediate value is less than `2³⁰` (`compress_eq`, `compress_arg_lt`);
* `Decompress_d(y) = (q · y + 2ᵈ⁻¹) >> d` for every `y < 2ᵈ`, which is less
  than `q` (`decompress_val`).

The compress formula is checked for each of the `q` inputs by the kernel.
-/

namespace VG.Proof.MlKem

open VG.Spec.MlKem

/-- The multiplier `M_d` of the compress formula: 315, 2520 and 161271 for
`d` = 1, 4 and 10. -/
def compressMul (d : Nat) : Nat := if d = 1 then 315 else if d = 4 then 2520 else 161271

/-- The addend of the compress formula, `2¹⁸ - 64`. -/
def compressAdd : Nat := 262080

theorem mem_compressWidths {d : Nat} (hd : d ∈ compressWidths) : d = 1 ∨ d = 4 ∨ d = 10 := by
  simpa [compressWidths] using hd

/-- `p x` for every `x < n`, as a `Nat.rec` over `Nat.beq`, which the kernel
evaluates much faster than the `Decidable` instance of a bounded `∀`. -/
def allBelow (n : Nat) (p : Nat → Bool) : Bool := Nat.rec true (fun i ih => p i && ih) n

theorem allBelow_spec {n : Nat} {p : Nat → Bool} (h : allBelow n p = true) :
    ∀ x < n, p x = true := by
  induction n with
  | zero => intro x hx; omega
  | succ n ih =>
    simp only [allBelow, Bool.and_eq_true] at h
    intro x hx
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
    · exact ih h.2 x hx
    · exact h.1

/-- The compress formula for width `d`, multiplier `m` and addend `a`, on
every `x < q`, from the kernel's check of each. -/
theorem compress_formula {d m a : Nat}
    (h : allBelow 3329 (fun x => Nat.beq (roundDiv (2 ^ d * x) 3329 % 2 ^ d)
      ((x * m + a) / 2 ^ 19 % 2 ^ d)) = true) (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ d * x) 3329 % 2 ^ d = (x * m + a) / 2 ^ 19 % 2 ^ d :=
  Nat.eq_of_beq_eq_true (allBelow_spec h x hx)

private theorem compress1 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 1 * x) 3329 % 2 ^ 1 = (x * 315 + 262080) / 2 ^ 19 % 2 ^ 1 :=
  compress_formula (by decide +kernel) x hx

private theorem compress4 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 4 * x) 3329 % 2 ^ 4 = (x * 2520 + 262080) / 2 ^ 19 % 2 ^ 4 :=
  compress_formula (by decide +kernel) x hx

private theorem compress10 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 10 * x) 3329 % 2 ^ 10 = (x * 161271 + 262080) / 2 ^ 19 % 2 ^ 10 :=
  compress_formula (by decide +kernel) x hx

/-- `Compress_d(x)` with a multiplication, an addition and a shift, for `d`
in `compressWidths`. -/
theorem compress_eq {d : Nat} (hd : d ∈ compressWidths) (x : Zq) :
    compress d x = (x.val * compressMul d + compressAdd) / 2 ^ 19 % 2 ^ d := by
  rcases mem_compressWidths hd with rfl | rfl | rfl
  · exact compress1 x.val x.isLt
  · exact compress4 x.val x.isLt
  · exact compress10 x.val x.isLt

/-- The value shifted in `compress_eq` fits in 30 bits. -/
theorem compress_arg_lt {d : Nat} (hd : d ∈ compressWidths) (x : Zq) :
    x.val * compressMul d + compressAdd < 2 ^ 30 := by
  have := val_lt x
  rcases mem_compressWidths hd with rfl | rfl | rfl
  · show x.val * 315 + 262080 < 2 ^ 30; omega
  · show x.val * 2520 + 262080 < 2 ^ 30; omega
  · show x.val * 161271 + 262080 < 2 ^ 30; omega

theorem compress_lt (d : Nat) (x : Zq) : compress d x < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos d)

/-- `Decompress_d(y)` with a multiplication, an addition and a shift, for
`1 ≤ d ≤ 11` and `y < 2ᵈ`: the result is less than `q`. -/
theorem decompress_val_of_le {d : Nat} (hd : 0 < d) (hd' : d ≤ 11) {y : Nat} (hy : y < 2 ^ d) :
    (decompress d y).val = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧ (q * y + 2 ^ (d - 1)) / 2 ^ d < q := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have hP : 2 ^ e ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by omega)
  have h : roundDiv (q * y) (2 ^ (e + 1)) = (q * y + 2 ^ e) / 2 ^ (e + 1) ∧
      (q * y + 2 ^ e) / 2 ^ (e + 1) < q := by
    rw [Nat.pow_succ] at hy ⊢
    simp only [roundDiv, q_eq]
    generalize 2 ^ e = P at *
    refine ⟨?_, (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)⟩
    rw [show 2 * (3329 * y) + P * 2 = 2 * (3329 * y + P) by omega, Nat.mul_div_mul_left _ _ (by decide)]
  rw [Nat.add_sub_cancel, decompress, ofNat_of_lt (h.1 ▸ h.2), h.1]
  exact ⟨rfl, h.2⟩

/-- `Decompress_d(y)` with a multiplication, an addition and a shift, for
`d` in `compressWidths` and `y < 2ᵈ`: the result is less than `q`. -/
theorem decompress_val {d : Nat} (hd : d ∈ compressWidths) {y : Nat} (hy : y < 2 ^ d) :
    (decompress d y).val = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧ (q * y + 2 ^ (d - 1)) / 2 ^ d < q :=
  decompress_val_of_le (by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide)
    (by rcases mem_compressWidths hd with rfl | rfl | rfl <;> decide) hy

end VG.Proof.MlKem
