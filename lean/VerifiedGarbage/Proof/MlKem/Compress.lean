import VerifiedGarbage.Proof.MlKem.Arith
import VerifiedGarbage.Spec.MlKem.Poly

/-!
# ML-KEM: Compress and Decompress without division, for every target

Untrusted: everything here is checked by Lean. `Compress_d` (4.7) divides
by `q`, and `Decompress_d` (4.8) by `2ᵈ`. For the widths ML-KEM-768 uses
(`compressWidths`: 1, 4 and 10), an implementation computes them with a
32-bit multiply-low, an addition and shifts:

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

private theorem compress1' : ∀ a < 53, ∀ b < 64,
    roundDiv (2 ^ 1 * (64 * a + b)) 3329 % 2 ^ 1 = ((64 * a + b) * 315 + 262080) / 2 ^ 19 % 2 ^ 1 := by
  decide +kernel

private theorem compress1 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 1 * x) 3329 % 2 ^ 1 = (x * 315 + 262080) / 2 ^ 19 % 2 ^ 1 := by
  have := compress1' (x / 64) (by omega) (x % 64) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

private theorem compress4' : ∀ a < 53, ∀ b < 64,
    roundDiv (2 ^ 4 * (64 * a + b)) 3329 % 2 ^ 4 = ((64 * a + b) * 2520 + 262080) / 2 ^ 19 % 2 ^ 4 := by
  decide +kernel

private theorem compress4 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 4 * x) 3329 % 2 ^ 4 = (x * 2520 + 262080) / 2 ^ 19 % 2 ^ 4 := by
  have := compress4' (x / 64) (by omega) (x % 64) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

private theorem compress10' : ∀ a < 53, ∀ b < 64,
    roundDiv (2 ^ 10 * (64 * a + b)) 3329 % 2 ^ 10 = ((64 * a + b) * 161271 + 262080) / 2 ^ 19 % 2 ^ 10 := by
  decide +kernel

private theorem compress10 (x : Nat) (hx : x < 3329) :
    roundDiv (2 ^ 10 * x) 3329 % 2 ^ 10 = (x * 161271 + 262080) / 2 ^ 19 % 2 ^ 10 := by
  have := compress10' (x / 64) (by omega) (x % 64) (Nat.mod_lt _ (by decide))
  rwa [Nat.div_add_mod] at this

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
`d` in `compressWidths` and `y < 2ᵈ`: the result is less than `q`. -/
theorem decompress_val {d : Nat} (hd : d ∈ compressWidths) {y : Nat} (hy : y < 2 ^ d) :
    (decompress d y).val = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧ (q * y + 2 ^ (d - 1)) / 2 ^ d < q := by
  have h : roundDiv (q * y) (2 ^ d) = (q * y + 2 ^ (d - 1)) / 2 ^ d ∧
      (q * y + 2 ^ (d - 1)) / 2 ^ d < q := by
    simp only [roundDiv, q_eq]
    rcases mem_compressWidths hd with rfl | rfl | rfl <;> constructor <;> omega
  rw [decompress, ofNat_of_lt (h.1 ▸ h.2), h.1]
  exact ⟨rfl, h.2⟩

end VG.Proof.MlKem
