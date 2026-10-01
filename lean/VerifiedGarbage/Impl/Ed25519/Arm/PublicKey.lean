import VerifiedGarbage.TCB.Arm.Isa
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Entry
import VerifiedGarbage.Impl.Ed25519.Arm.Whole.Wipe
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarBase
import VerifiedGarbage.Impl.Sha512.Arm.Stream
import VerifiedGarbage.Spec.Ed25519.Contract
import VerifiedGarbage.Spec.Sha512.Contract

namespace VG.Impl.Ed25519.Arm.PublicKey
open VG.Arm

def pruneLow : List Instr :=
  [.movw .r1 0xfff8, .movt .r1 0xffff, .dp .and .r0 .r0 (.reg .r1)]
def pruneHigh : List Instr :=
  [.movw .r1 0xffff, .movt .r1 0x3fff, .dp .and .r0 .r0 (.reg .r1),
    .movw .r1 0, .movt .r1 0x4000, .dp .orr .r0 .r0 (.reg .r1)]
def pruneWord (k : Nat) : List Instr :=
  [.ldrSp .r0 (184 + 4 * k)] ++ (if k = 0 then pruneLow else if k = 7 then pruneHigh else []) ++
    [.addSp .r12 24, .str .r0 .r12 (4 * k)]
def prune : List Instr := (List.range 8).flatMap pruneWord

open VG.Impl.Ed25519.Arm.Whole

def initArgs : List Instr := setup [(.r0, .caller 2 0)] []
def updateArgs : List Instr := setup [(.r0, .caller 2 0), (.r2, .const 0), (.r3, .const 0)]
  [.caller 1 0, .const 32, .caller 2 192]
def finalizeArgs : List Instr := setup [(.r0, .caller 2 0), (.r2, .const 32), (.r3, .const 0)]
  [.frame 184, .caller 2 192]
def baseArgs : List Instr := setup [(.r0, .caller 0 0), (.r1, .frame 24), (.r2, .caller 2 0)] []
def hash : Prog isa :=
  .seq (callWith initArgs Spec.Sha512.init512Api.name (Sha512.Arm.Stream.init Spec.Sha512.H0_512))
    (.seq (callWith updateArgs Spec.Sha512.updateApi.name Sha512.Arm.Stream.update)
      (callWith finalizeArgs Spec.Sha512.finalizeApi.name Sha512.Arm.Stream.finalize))
def wipe : List Instr := zeroWords 6 56
def body : Prog isa := .seq hash (.seq (.block prune)
  (.seq (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) (.block wipe)))
def code : Prog isa := wrap 3 body

end VG.Impl.Ed25519.Arm.PublicKey
