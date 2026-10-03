import VerifiedGarbage.Impl.Argon2.X86.Initial

/-!
# Argon2 on x86 (32-bit): memory initialization

The whole matrix is cleared, then `vg_argon2_hprime` computes the first two
blocks of every lane, B[lane][column] = H′(1024, H₀ ‖ LE32(column) ‖
LE32(lane)), from the 72 bytes at the start of the locals (`ebp`), with
`scratch` as its working space. `esi` counts the lanes and `edi` points to
the block being initialized; both are kept across the calls, as `ebp` is.
-/

namespace VG.Impl.Argon2.X86.Derive

open VG.X86
open VG.Impl.Sha512.X86 (at_)

def hPrimeName : String := "vg_argon2_hprime"

/-- `hprime(ebp, eax, edi, ecx, edx)`, its arguments pushed last to first. -/
def hPrimeCall : Prog isa :=
  .frame (.push [.edx, .ecx, .edi, .eax, .ebp]) (.call hPrimeName HPrime.code) (.pop .eax 5)

/-- Zero `blocks · 256` words from `memory` on. -/
def clearSetup : List Instr :=
  [.mov .edi (fr (argOff memoryArg)), .mov .ecx (fr (argOff blocksArg))] ++
    List.replicate 8 (.alu .add .ecx (.reg .ecx)) ++ [.mov .eax (.imm 0)]

def clearWord : List Instr := [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .sub .ecx (.imm 1)]

def clear : Prog isa := .seq (.block clearSetup) (.loop (.block clearWord) .ne)

/-- B[esi][column], at `edi`. -/
def initBlock (column : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 column)), .store (at_ .ebp columnOff) .eax,
      .store (at_ .ebp laneWordOff) .esi, .mov .eax (.imm 72), .mov .ecx (.imm 1024),
      .mov .edx (fr (argOff scratchArg))])
    hPrimeCall

/-- The next lane's first block, and the comparison of the lane with the
lane count. -/
def nextLane : List Instr :=
  [.mov .eax (fr strideOff), .alu .add .edi (.reg .eax), .alu .sub .edi (.imm 1024),
    .alu .add .esi (.imm 1), .alu .cmp .esi (fr (argOff lanesArg))]

def initLane : Prog isa :=
  .seq (initBlock 0) (.seq (.block [.alu .add .edi (.imm 1024)]) (.seq (initBlock 1) (.block nextLane)))

def memoryInit : Prog isa :=
  .seq clear (.seq (.block [.mov .edi (fr (argOff memoryArg)), .mov .esi (.imm 0)])
    (.loop initLane .b))

end VG.Impl.Argon2.X86.Derive
