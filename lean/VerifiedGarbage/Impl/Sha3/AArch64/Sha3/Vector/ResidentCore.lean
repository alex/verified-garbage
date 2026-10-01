import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.AbsorbBlock
import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector.Boundary

namespace VG.Impl.Sha3.AArch64.Sha3.Vector.Resident

open VG VG.AArch64
open VG.Impl.Sha3.AArch64.Sha3.Vector

/-- The rate is public and is one of the five FIPS202 rates. Selecting only
the input XOR here lets every rate share a single copy of the round body. -/
def xorRate : Prog isa :=
  [72,104,136,144].foldr (fun rate rest =>
    .seq (.block [.subImm .x .x7 .x6 rate])
      (.ite (.zero .x .x7) (.block (absorbBlock rate)) rest))
    (.block (absorbBlock 168))

/-- `x7=0` admits a complete block. Extremely large lengths can conservatively
take the generic path; no data-dependent branch is involved. -/
def test : List Instr := [.sub .x .x7 .x4 .x6,.lsr .x .x7 .x7 63]

def advance : List Instr := [.add .x .x3 .x3 .x6,.sub .x .x4 .x4 .x6]

def body : Prog isa := .seq xorRate (.block (rounds ++ advance ++ test))

/-- Enter with at least one complete block. Save and load the state once,
consume whole blocks without memory round trips, then store it and restore
the caller's SIMD registers before handling the remaining partial block. -/
def bulk : Prog isa :=
  .seq (.block (save ++ load))
    (.seq (.loop body (.zero .x .x7)) (.block (store ++ restore)))

end VG.Impl.Sha3.AArch64.Sha3.Vector.Resident
