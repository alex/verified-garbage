import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.ResidentCore
import VerifiedGarbage.Impl.Sha3.AArch64.Stream

namespace VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64 (mov Callee)

/-- An optional absorber for a fully proved permutation backend. Nonaligned
input uses that backend's ordinary streaming implementation. -/
def bulkPrefix : Prog isa :=
  .ite (.zero .x .x2)
    (.seq (.block (mov .x6 .x1 :: test))
      (.ite (.zero .x .x7)
        (.seq (.block [mov .x1 .x5])
          (.seq bulk (.block [mov .x1 .x6])))
        (.block [])))
    (.block [])

def absorb (c : Callee) : Prog isa :=
  .seq bulkPrefix (Stream.absorbGenericWith c)

end VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
