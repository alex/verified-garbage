import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.PackedLanes

namespace VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Spec.MlDsa (Poly Zq zetas)
open VG.Proof.MlDsa.Arith
set_option linter.unusedSimpArgs false

/-- A packed batch reads only coefficients not visited by earlier batches. -/
theorem packed_input {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op)
    (F : Poly) (zi : Nat → Nat) (len : Nat) (hlen : len = 1 ∨ len = 2)
    {u r : Nat} (hu : u < 32) (hr : r < 8) :
    (layF blk F len zi ((4/len)*u))[8*u+r]! = F[8*u+r]! := by
  rcases hlen with rfl | rfl
  · rw [layF1_get hblk F zi (by omega) (by omega)]
    simp only [Nat.div_one]; rw [ite_eq_right (by omega)]
  · rw [layF2_get hblk F zi (by omega) (by omega)]
    simp only [Nat.reduceDiv]; rw [ite_eq_right (by omega)]

/-- Lane indices and coefficient indices agree for both packed layer sizes. -/
theorem packed_indices (len : Nat) (hlen : len = 1 ∨ len = 2) (u r : Nat) :
    lower len (lane len r) = r-r%(2*len)+r%len ∧
    (4/len)*u + lane len r/len = (8*u+r)/(2*len) := by
  rcases hlen with rfl | rfl <;> simp only [lower,lane,Nat.div_one,Nat.mod_one,
    Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul,Nat.reduceDiv] <;> omega

/-- One packed batch has the same result as its corresponding scalar blocks. -/
theorem packed_batch_get {blk : Poly → Nat → Nat → Nat → Nat → Poly}
    {op : Zq → Zq → Zq → Zq × Zq} (hblk : BlkOk blk op)
    (F : Poly) (zi : Nat → Nat) (len : Nat) (hlen : len = 1 ∨ len = 2)
    {u j : Nat} (hu : u < 32) (hj : j < 256) :
    let G := layF blk F len zi ((4/len)*u)
    let A := fun e => (op G[8*u+lower len e]! G[8*u+lower len e+len]!
      (zetas (zi ((4/len)*u+e/len)))).1
    let B := fun e => (op G[8*u+lower len e]! G[8*u+lower len e+len]!
      (zetas (zi ((4/len)*u+e/len)))).2
    (layF blk F len zi ((4/len)*(u+1)))[j]! =
      if 8*u ≤ j ∧ j < 8*u+8 then result len A B (j-8*u) else G[j]! := by
  dsimp only
  by_cases hin : 8*u ≤ j ∧ j < 8*u+8
  · rw [ite_eq_left hin]
    have hr : j-8*u < 8 := by omega
    have hi := packed_indices len hlen u (j-8*u)
    have hlow : lower len (lane len (j-8*u)) < 8 := by
      rcases hlen with rfl | rfl <;> simp only [lower,lane,Nat.div_one,Nat.mod_one,
        Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul] <;> omega
    have hhigh : lower len (lane len (j-8*u))+len < 8 := by
      rcases hlen with rfl | rfl <;> simp only [lower,lane,Nat.div_one,Nat.mod_one,
        Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul] <;> omega
    unfold result
    dsimp only
    rw [packed_input hblk F zi len hlen hu hlow]
    rw [show 8*u+lower len (lane len (j-8*u))+len =
      8*u+(lower len (lane len (j-8*u))+len) by omega,
      packed_input hblk F zi len hlen hu hhigh]
    have hz : (4/len)*u+lane len (j-8*u)/len = j/(2*len) := by
      rw [hi.2,show 8*u+(j-8*u) = j by omega]
    rw [hz]
    simp only [← Nat.add_assoc]
    rcases hlen with rfl | rfl
    · rw [layF1_get hblk F zi (by omega) hj,ite_eq_left (by omega)]
      by_cases he : j%2 = 0
      · simp only [ite_eq_left he]
        rw [ite_eq_left (by omega),show 8*u+lower 1 (lane 1 (j-8*u)) = j by
          simp only [lower,lane,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul]; omega]
      · simp only [ite_eq_right he]
        rw [ite_eq_right (by omega),show 8*u+lower 1 (lane 1 (j-8*u)) = j-1 by
          simp only [lower,lane,Nat.div_one,Nat.mod_one,Nat.mul_one,Nat.one_mul,Nat.add_zero,Nat.reduceMul]; omega]
        simp only [Nat.reduceMul]
        rw [show j-1+1 = j by omega]
    · rw [layF2_get hblk F zi (by omega) hj,ite_eq_left (by omega)]
      by_cases he : j%4 < 2
      · simp only [ite_eq_left he]
        rw [ite_eq_left (by omega),show 8*u+lower 2 (lane 2 (j-8*u)) = j by
          simp only [lower,lane,Nat.reduceMul]; omega]
      · simp only [ite_eq_right he]
        rw [ite_eq_right (by omega),show 8*u+lower 2 (lane 2 (j-8*u)) = j-2 by
          simp only [lower,lane,Nat.reduceMul]; omega]
        simp only [Nat.reduceMul]
        rw [show j-2+2 = j by omega]
  · rw [ite_eq_right hin]
    rcases hlen with rfl | rfl
    · rw [layF1_get hblk F zi (by omega) hj,layF1_get hblk F zi (by omega) hj]
      simp only [Nat.div_one]
      by_cases h : j < 8*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]
    · rw [layF2_get hblk F zi (by omega) hj,layF2_get hblk F zi (by omega) hj]
      simp only [Nat.reduceDiv]
      by_cases h : j < 8*u <;> simp (disch := omega) only [ite_eq_left,ite_eq_right]

end VG.Proof.MlDsa.AArch64.Arith.Neon
