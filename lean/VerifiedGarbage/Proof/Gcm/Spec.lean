import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Spec.Gcm

/-!
# GCM: lemmas about the specification
-/

namespace VG.Proof.Gcm

open VG.Spec.Gcm

/-- Step `i` of Algorithm 1 (`Spec.Gcm.mul`) on `(Z, V)`, for the factor `x`. -/
def mulStep (x : Block) (zv : Block × Block) (i : Nat) : Block × Block :=
  (if x.getMsbD i then zv.1 ^^^ zv.2 else zv.1,
   if zv.2.getLsbD 0 then (zv.2 >>> 1) ^^^ R else zv.2 >>> 1)

/-- The first `k` steps of Algorithm 1 for `x • y`. -/
def mulSteps (x y : Block) (k : Nat) : Block × Block :=
  (List.range k).foldl (mulStep x) (0, y)

theorem mul_eq (x y : Block) : mul x y = (mulSteps x y 128).1 := rfl

theorem mulSteps_zero (x y : Block) : mulSteps x y 0 = (0, y) := rfl

theorem mulSteps_succ (x y : Block) (k : Nat) :
    mulSteps x y (k + 1) = mulStep x (mulSteps x y k) k := by
  simp only [mulSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem ghashFrom_blocksAt_succ (h y : Block) (m : Mem) (p : Addr) (i : Nat) :
    ghashFrom h y (blocksAt m p (i + 1)) =
      mul (ghashFrom h y (blocksAt m p i) ^^^ blockAt m (p + BitVec.ofNat 64 (16 * i))) h := by
  simp only [ghashFrom, blocksAt, List.range_succ, List.map_append, List.foldl_append,
    List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]

theorem ghashFrom_blocksAt_zero (h y : Block) (m : Mem) (p : Addr) :
    ghashFrom h y (blocksAt m p 0) = y := rfl

/-- `blockAt` only depends on the 16 bytes of the block. -/
theorem blockAt_congr {m m' : Mem} {p : Addr}
    (h : ∀ i < 16, m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i)) :
    blockAt m' p = blockAt m p := by
  simp only [blockAt, Spec.Aes.bytesAt]
  congr 1
  exact List.map_congr_left fun i hi => h i (List.mem_range.mp hi)

theorem toNat_append {n k : Nat} (x : BitVec n) (y : BitVec k) :
    (x ++ y).toNat = x.toNat * 2 ^ k + y.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt y.isLt, Nat.shiftLeft_eq]

/-- A block from its 16 bytes, the first the most significant. -/
theorem ofBytes_16 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Byte) :
    ofBytes [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] =
      ((b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) ++
        (b8 ++ b9 ++ b10 ++ b11 ++ b12 ++ b13 ++ b14 ++ b15 : BitVec 64) : BitVec 128) := by
  apply BitVec.eq_of_toNat_eq
  simp only [ofBytes, List.foldl_cons, List.foldl_nil, toNat_append, BitVec.toNat_ofNat]
  have := b0.isLt; have := b1.isLt; have := b2.isLt; have := b3.isLt; have := b4.isLt
  have := b5.isLt; have := b6.isLt; have := b7.isLt; have := b8.isLt; have := b9.isLt
  have := b10.isLt; have := b11.isLt; have := b12.isLt; have := b13.isLt; have := b14.isLt
  have := b15.isLt
  omega

end VG.Proof.Gcm
