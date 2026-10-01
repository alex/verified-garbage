import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Entry
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Setup
import VerifiedGarbage.Impl.Ed25519.AArch64.Whole.Wipe
import VerifiedGarbage.Impl.Ed25519.AArch64.ScalarBase
import VerifiedGarbage.Impl.Sha512.AArch64.Stream
import VerifiedGarbage.Spec.Sha512.Contract

namespace VG.Impl.Ed25519.AArch64.PublicKey
open VG.AArch64

/-- Clear the low three bits of the first digest word. -/
def pruneLow : List Instr :=
  [.movz .x .x10 0xfff8 0, .movk .x .x10 0xffff 1, .movk .x .x10 0xffff 2,
    .movk .x .x10 0xffff 3, .logic .and .x .x9 .x9 .x10]

/-- Clear bit 255 and set bit 254 in the fourth digest word. -/
def pruneHigh : List Instr :=
  [.movz .x .x10 0xffff 0, .movk .x .x10 0xffff 1, .movk .x .x10 0xffff 2,
    .movk .x .x10 0x3fff 3, .logic .and .x .x9 .x9 .x10,
    .movz .x .x10 0x4000 3, .logic .orr .x .x9 .x9 .x10]

/-- Copy and prune word `k` from the seed digest to the scalar. -/
def pruneWord (k : Nat) : List Instr :=
  [.ldrSp .x9 (192 + 8 * k)] ++
    (if k = 0 then pruneLow else if k = 3 then pruneHigh else []) ++
    [.addSp .x15 (32 + 8 * k), .str .x .x9 .x15 0]

def prunePrefix (n : Nat) : List Instr := (List.range n).flatMap pruneWord

def prune : List Instr := prunePrefix 4

open VG.Impl.Ed25519.AArch64.Whole (setup callWith)

def initArgs : List Instr := setup [(.x0, .caller 2 0)]
def updateArgs : List Instr := setup
  [(.x0, .caller 2 0), (.x1, .const 0), (.x2, .caller 1 0), (.x3, .const 32), (.x4, .caller 2 192)]
def finalizeArgs : List Instr := setup
  [(.x0, .caller 2 0), (.x1, .const 32), (.x2, .frame 192), (.x3, .caller 2 192)]
def baseArgs : List Instr := setup [(.x0, .caller 0 0), (.x1, .frame 32), (.x2, .caller 2 0)]

def hash (f : Prog isa) (suffix : String) : Prog isa :=
  .seq (callWith initArgs Spec.Sha512.init512Api.name (Sha512.AArch64.Stream.init Spec.Sha512.H0_512))
    (.seq (callWith updateArgs (Spec.Sha512.updateApi.name ++ suffix) (Sha512.AArch64.Stream.updateWith f))
      (callWith finalizeArgs (Spec.Sha512.finalizeApi.name ++ suffix) (Sha512.AArch64.Stream.finalizeWith f)))

def wipe : List Instr := Whole.zeroWords 4 28

def body (f : Prog isa) (suffix : String) : Prog isa :=
  .seq (hash f suffix) (.seq (.block prune)
    (.seq (callWith baseArgs "vg_ed25519_scalar_base" scalarBase) (.block wipe)))

def code (f : Prog isa) (suffix : String) : Prog isa := Whole.wrap (body f suffix)

end VG.Impl.Ed25519.AArch64.PublicKey
