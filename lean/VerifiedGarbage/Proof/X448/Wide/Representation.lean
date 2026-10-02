import VerifiedGarbage.Proof.X448.Wide.Limbs

/-!
# Headroom-aware X448 field representation

Untrusted: this is an internal arithmetic contract for an eight-word backend.
A representative has a value modulo p and a separate, explicit coefficient
bound. Weak reduction need not normalize every coefficient below the radix.
The public RFC 7748 contract and existing backend contract are unchanged.
-/
namespace VG.Proof.X448.Wide.Representation
open VG.Spec.X448
open VG.Proof.X448 (toFe)

/-- Coefficient headroom, independent of the represented field value. -/
def Within (bound : Nat) (f : Nat → Nat) : Prop := ∀ i < 8, f i < bound

/-- The same field element may have many noncanonical representatives. -/
def Represents (f : Nat → Nat) (x : Fe) : Prop := toFe (valN f 8) = x

/-- Conservative weak bound, closed under the add/sub contracts below. -/
def weakBound : Nat := radix + 32

/-- The contract an eight-word weakly reduced field operation maintains. -/
structure Weak (f : Nat → Nat) (x : Fe) : Prop where
  value : Represents f x
  limbs : Within weakBound f

/-- Distribute old carries independently, then fold the top one into 0 and 4.
This is a mathematical weak-reduction schedule, not the existing serial pass
and not a transcription of OpenSSL's instruction schedule. -/
def weakReduce (f : Nat → Nat) (i : Nat) : Nat :=
  f i % radix + (if i = 0 then f 7 / radix else f (i - 1) / radix) +
    (if i = 4 then f 7 / radix else 0)

theorem weakReduce_val (f : Nat → Nat) :
    valN (weakReduce f) 8 + P * (f 7 / radix) = valN f 8 := by
  have h0 := Nat.mod_add_div (f 0) radix
  have h1 := Nat.mod_add_div (f 1) radix
  have h2 := Nat.mod_add_div (f 2) radix
  have h3 := Nat.mod_add_div (f 3) radix
  have h4 := Nat.mod_add_div (f 4) radix
  have h5 := Nat.mod_add_div (f 5) radix
  have h6 := Nat.mod_add_div (f 6) radix
  have h7 := Nat.mod_add_div (f 7) radix
  simp only [radix, Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7
  have hp : P = radix ^ 8 - radix ^ 4 - 1 := by decide +kernel
  simp only [valN, weakReduce, Nat.reduceSub, Nat.reduceEqDiff, ite_true, ite_false,
    Nat.pow_zero, Nat.zero_add, Nat.one_mul, Nat.add_zero, hp, radix, Nat.reducePow, Nat.reduceSub]
  omega

theorem weakReduce_mod (f : Nat → Nat) :
    valN (weakReduce f) 8 % P = valN f 8 % P := by
  rw [← weakReduce_val f, Nat.add_mul_mod_self_left]

theorem weakReduce_represents {f : Nat → Nat} {x : Fe} (h : Represents f x) :
    Represents (weakReduce f) x := by
  exact (VG.Proof.X448.toFe_congr (weakReduce_mod f)).trans h

/-- Public integer headroom controls both old carries at each output limb. -/
theorem weakReduce_bound {f : Nat → Nat} {h : Nat}
    (hf : Within (radix * h) f) (hh : 1 ≤ h) :
    Within (radix + 2 * (h - 1)) (weakReduce f) := by
  intro i hi
  have low := Nat.mod_lt (f i) (show 0 < radix by decide)
  have top : f 7 / radix < h := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
    simpa only [Nat.mul_comm] using hf 7 (by decide))
  have prev : f (i - 1) / radix < h := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by
    simpa only [Nat.mul_comm] using hf (i - 1) (by omega))
  simp only [weakReduce]
  split <;> split <;> omega

/-- Addition may enter the reducer with almost three radix units of headroom. -/
theorem add_weak_bound {f g : Nat → Nat} (hf : Within weakBound f) (hg : Within weakBound g) :
    Within weakBound (weakReduce (fun i => f i + g i)) := by
  have cap : Within (radix * 3) (fun i => f i + g i) := by
    intro i hi
    have a := hf i hi; have b := hg i hi
    simp only [weakBound, radix] at a b ⊢
    omega
  have out := weakReduce_bound cap (by decide : 1 ≤ 3)
  intro i hi
  exact Nat.lt_of_lt_of_le (out i hi) (by simp only [weakBound]; omega)

/-- Four times p leaves room for weak limbs during nonnegative subtraction. -/
def bias (i : Nat) : Nat := if i = 4 then 4 * radix - 8 else 4 * radix - 4

def difference (f g : Nat → Nat) (i : Nat) : Nat := f i + bias i - g i

theorem difference_weak_bound {f g : Nat → Nat} (hf : Within weakBound f) :
    Within weakBound (weakReduce (difference f g)) := by
  have cap : Within (radix * 6) (difference f g) := by
    intro i hi
    have a := hf i hi
    simp only [difference, bias]
    split <;> simp only [weakBound, radix] at a ⊢ <;> omega
  have out := weakReduce_bound cap (by decide : 1 ≤ 6)
  intro i hi
  exact Nat.lt_of_lt_of_le (out i hi) (by simp only [weakBound]; omega)

theorem add_ok {f g : Nat → Nat} {x y : Fe} (hf : Weak f x) (hg : Weak g y) :
    Weak (weakReduce (fun i => f i + g i)) (x + y) := by
  refine ⟨?_, add_weak_bound hf.limbs hg.limbs⟩
  unfold Represents
  have h := VG.Proof.X448.toFe_add (a := valN f 8) (b := valN g 8)
    (c := valN (weakReduce (fun i => f i + g i)) 8) (by
      rw [weakReduce_mod, valN_add])
  exact h.trans (congrArg₂ (· + ·) hf.value hg.value)

theorem bias_val : valN bias 8 = 4 * P := by decide +kernel

theorem bias_ge (i : Nat) : weakBound ≤ bias i := by
  simp only [bias]
  split <;> decide +kernel

theorem difference_val {f g : Nat → Nat} (hg : Within weakBound g) :
    valN (difference f g) 8 + valN g 8 = valN f 8 + 4 * P := by
  rw [← valN_add]
  have eq : valN (fun i => difference f g i + g i) 8 =
      valN (fun i => f i + bias i) 8 := by
    apply valN_congr
    intro i hi
    have h := hg i hi
    have b := bias_ge i
    simp only [difference]
    omega
  rw [eq, valN_add, bias_val]

theorem sub_ok {f g : Nat → Nat} {x y : Fe} (hf : Weak f x) (hg : Weak g y) :
    Weak (weakReduce (difference f g)) (x - y) := by
  refine ⟨?_, difference_weak_bound hf.limbs⟩
  unfold Represents
  have hm : (valN (weakReduce (difference f g)) 8 + valN g 8) % P = valN f 8 % P := by
    rw [Nat.add_mod, weakReduce_mod, ← Nat.add_mod, difference_val hg.limbs,
      Nat.mul_comm 4 P, Nat.add_mul_mod_self_left]
  exact (VG.Proof.X448.toFe_sub hm).trans (congrArg₂ (· - ·) hf.value hg.value)

/-- Existing full normalization is a conversion from broad coefficients to
normalized limbs; normalized output is also a valid weak representative. -/
theorem normalize_within_weak (f : Nat → Nat) : Within weakBound (normalized f) := by
  intro i _
  exact Nat.lt_trans (digit_lt _ i) (by simp only [weakBound]; omega)

/-- Full normalization preserves the field value while tightening the bound. -/
theorem normalize_ok {f : Nat → Nat} {x : Fe}
    (h : Within (2 ^ 118) f) (hx : Represents f x) : Weak (normalized f) x :=
  ⟨(VG.Proof.X448.toFe_congr (normalized_mod h)).trans hx, normalize_within_weak f⟩

/-- The second serial carry pass has at most one carry-out. -/
theorem second_carry {f : Nat → Nat} (h : Within (2 ^ 118) f) :
    carry (folded f) 8 ≤ 1 := by
  have c0 := carry_bound h
  have v0 := valN_lt (n := 8) (fun i _ => digit_lt f i)
  have e1 := pass_eq (folded f) 8
  rw [folded_val] at e1
  change valN (digit f) 8 < full at v0
  change valN (digit (folded f)) 8 + full * carry (folded f) 8 = _ at e1
  have small : (half + 1) * (2 ^ 63 + 1) < full := by decide +kernel
  by_contra hc
  have hb := Nat.mul_le_mul_left (half + 1) (Nat.le_of_lt c0)
  have hp := Nat.mul_le_mul_left full (show 2 ≤ carry (folded f) 8 from by omega)
  omega

/-- Two carry passes and folds suffice for a weak field representative. -/
theorem twice_weak {f : Nat → Nat} (h : Within (2 ^ 118) f) :
    Within weakBound (folded (folded f)) := by
  have hc := second_carry h
  intro i _
  have hd := digit_lt (folded f) i
  simp only [folded, weakBound]
  split <;> omega

theorem twice_mod (f : Nat → Nat) :
    valN (folded (folded f)) 8 % P = valN f 8 % P := by
  rw [folded_mod, folded_mod]

end VG.Proof.X448.Wide.Representation
