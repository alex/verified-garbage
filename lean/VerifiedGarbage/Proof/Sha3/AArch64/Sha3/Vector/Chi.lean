import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rho

namespace VG.Proof.Sha3.AArch64.Sha3.Vector

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector
open VG.Proof.Sha3 (B)

def chiWord (A : Spec.Sha3.State) (i : Nat) : BitVec 64 :=
  B A (i % 5) (i / 5) ^^^
    (B A ((i % 5 + 2) % 5) (i / 5) &&& ~~~(B A ((i % 5 + 1) % 5) (i / 5)))

def CLanes (σ : Low) (A : Spec.Sha3.State) : Prop := ∀ i < 25, σ (vreg i) = chiWord A i

theorem chi_lanes (σ : Low) (A : Spec.Sha3.State) (hB : BLanes σ A) :
    CLanes (runLow chi σ) A := by
  have b0 := hB 0 (by decide)
  have b1 := hB 1 (by decide)
  have b2 := hB 2 (by decide)
  have b3 := hB 3 (by decide)
  have b4 := hB 4 (by decide)
  have b5 := hB 5 (by decide)
  have b6 := hB 6 (by decide)
  have b7 := hB 7 (by decide)
  have b8 := hB 8 (by decide)
  have b9 := hB 9 (by decide)
  have b10 := hB 10 (by decide)
  have b11 := hB 11 (by decide)
  have b12 := hB 12 (by decide)
  have b13 := hB 13 (by decide)
  have b14 := hB 14 (by decide)
  have b15 := hB 15 (by decide)
  have b16 := hB 16 (by decide)
  have b17 := hB 17 (by decide)
  have b18 := hB 18 (by decide)
  have b19 := hB 19 (by decide)
  have b20 := hB 20 (by decide)
  have b21 := hB 21 (by decide)
  have b22 := hB 22 (by decide)
  have b23 := hB 23 (by decide)
  have b24 := hB 24 (by decide)
  simp only [breg, List.getD_cons_succ, List.getD_cons_zero, Nat.reduceMod, Nat.reduceDiv] at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24
  -- One `simp` for all the lanes, which simplifies `runLow chi σ` once.
  refine forall_lt_25 ?_
  simp only [and_self, runLow, chi, List.foldl_cons, List.foldl_nil, opLow, put, vreg,
      List.getD_cons_succ, List.getD_cons_zero, reduceCtorEq, ite_true, ite_false,
      b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, chiWord, Nat.reduceMod, Nat.reduceDiv, Nat.reduceAdd]

theorem chiWord_out (A : Spec.Sha3.State) (rc : BitVec 64) (i : Nat) (hi : i < 25) :
    (if i = 0 then chiWord A i ^^^ rc else chiWord A i) =
      (VG.Proof.Sha3.outState A rc)[i] := by
  simp only [VG.Proof.Sha3.outState, Vector.getElem_ofFn, VG.Proof.Sha3.out, chiWord]
  have hz : i % 5 = 0 ∧ i / 5 = 0 ↔ i = 0 := by omega
  simp only [hz]
  have hn (v : BitVec 64) : v ^^^ 0xffffffffffffffff = ~~~v := BitVec.xor_allOnes
  simp only [hn, BitVec.and_comm, BitVec.xor_comm]

end VG.Proof.Sha3.AArch64.Sha3.Vector
