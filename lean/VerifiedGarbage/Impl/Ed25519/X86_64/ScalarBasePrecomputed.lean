import VerifiedGarbage.Impl.Ed25519.X86_64.BaseCheckpoints
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify

/-! Fixed-base multiplication with exact, precomputed checkpoint coordinates. -/
namespace VG.Impl.Ed25519.X86_64
open VG.X86_64

def baseCheckpointStore (i : Nat) : List Instr :=
  constPoint (baseCheckpoint i) ++ pointTableWrite (1280 + 128 * i)

def baseCheckpointStores (n : Nat) : List Instr :=
  (List.range n).flatMap baseCheckpointStore

def baseMultiplyPrecomputedInit : Prog isa :=
  .seq (.block (baseCheckpointStores 16))
    (.seq (.block (constPoint Spec.Ed25519.identity)) (.block (mulCounterInit 16)))

def baseMultiplyPrecomputed : Prog isa :=
  .seq baseMultiplyPrecomputedInit (.loop pointMulBatch .ne)

def scalarBasePrecomputedEngine : Prog isa :=
  .seq scalarBasePrepare (.seq baseMultiplyPrecomputed pointEncode)

def scalarBase_precomputed : Prog isa :=
  scalarBaseWith scalarBasePrecomputedEngine

end VG.Impl.Ed25519.X86_64
