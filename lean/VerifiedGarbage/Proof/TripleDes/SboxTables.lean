import VerifiedGarbage.Spec.TripleDes
import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.Framework.Lit

/-!
# The S-boxes' inputs and outputs, as truth tables

Every target's S-box code, of DES and of TDEA-CMAC, is checked on all 64
inputs at once, against these (`Proof/TripleDes/<target>/Sbox.lean`,
`Proof/CmacTripleDes/<target>/Round.lean`): the kernel evaluates them once,
here (`materialize_table`), rather than evaluate the specification's S-boxes
on every input again for every target.
-/

namespace VG.Proof.TripleDes

open VG.Bitslice

/-- Bit `k` of every input `c < 64`. -/
def inputTable (k : Nat) : Nat := tableOf (fun c => c.testBit k) 64

/-- Output bit `j` of box `i`, on every input `c < 64`. -/
def outputTable (i j : Nat) : Nat :=
  tableOf (fun c => (Spec.TripleDes.sBox i (BitVec.ofNat 6 c)).getLsbD j) 64

theorem testBit_outputTable {i j c : Nat} (hc : c < 64) :
    (outputTable i j).testBit c = (Spec.TripleDes.sBox i (BitVec.ofNat 6 c)).getLsbD j := by
  rw [outputTable, testBit_tableOf, decide_eq_true hc, Bool.true_and]

end VG.Proof.TripleDes

namespace VG

materialize_table Proof.TripleDes.inputTable 6
materialize_table Proof.TripleDes.outputTable 8 4

end VG
