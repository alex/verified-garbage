import VerifiedGarbage.Impl.MlKem.X86.Basic
import VerifiedGarbage.Impl.Sha3.X86.Stream

/-!
# ML-KEM on x86 (32-bit): `vg_mlkem_sample_ntt`

`sampleNTT(seed, a, scratch) -> eax`: SHAKE128 of the 34 bytes at `seed`,
by the verified `vg_keccak_absorb`, `vg_keccak_pad` and `vg_keccak_squeeze`
from the all-zero state, squeezing 840 bytes (the `3 · 280` bytes of
`minIterations = 280` iterations) at once; then the 280 iterations of the
loop of Algorithm 7 on them, which stop accepting coefficients once there
are 256. Returns 1 if there are 256, and 0 if not.

It saves its caller's `ebx`, `esi`, `edi` and `ebp` in a frame of 16 bytes
(`leaf`), and keeps `esi` = `scratch` across the calls (which preserve it).
Each call pushes its arguments (in registers) in a frame of its own, popped
into `eax` when it returns (`callWith`). `scratch` (2048 bytes) is laid out
as:

* `[0, 840)`: the SHAKE128 output;
* `[840, 1040)`: the Keccak state;
* `[1040, 1680)`: the Keccak functions' working space.

The loop keeps `esi` = the next chunk of output, `edi` = the next
coefficient of `a`, `ecx` = the coefficients accepted, `ebp` = the
iterations left. The candidates of a chunk are computed in `eax` and `ebx`
(as in `decode12`). The loop's branches and the addresses it writes depend
on the SHAKE128 output, and so on the seed, which the contract declares
that it may leak; everything else depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86

open VG.X86

/-- `++`, grouping to the right. -/
local infixr:65 " +++ " => HAppend.hAppend

/-- Where the Keccak state and working space are in `scratch`. -/
def smpSt : Nat := 840
def smpWk : Nat := 1040

/-- `ebx` at the Keccak state (at `esi + st`), `eax = 0`, `ecx = 50`. -/
def zeroInit (st : Nat) : List Instr :=
  [.mov .ebx (.reg .esi), .alu .add .ebx (.imm (BitVec.ofNat 32 st)), .mov .eax (.imm 0), .mov .ecx (.imm 50)]

/-- Zero the word at `ebx`, and on to the next. -/
def zeroBody : List Instr := [.store (at_ .ebx 0) .eax, .alu .add .ebx (.imm 4), .alu .sub .ecx (.imm 1)]

/-- Zero the 200 bytes of the Keccak state at `esi + st`. -/
def zeroSt (st : Nat) : Prog isa := .seq (.block (zeroInit st)) (.loop (.block zeroBody) .ne)

/-- `absorb(state, 168, 0, seed, 34, work)`'s arguments. -/
def smpAbsorbArgs : List Instr :=
  [.mov .eax (.reg .esi), .alu .add .eax (.imm (BitVec.ofNat 32 smpSt)), .mov .ecx (.imm 168),
    .mov .edx (.imm 0), .mov .ebx (.mem (at_ .esp 20)), .mov .ebp (.imm 34), .mov .edi (.reg .esi),
    .alu .add .edi (.imm (BitVec.ofNat 32 smpWk))]

/-- `pad(state, 168, 34, 0x1f, work)`'s arguments. -/
def smpPadArgs : List Instr :=
  [.mov .eax (.reg .esi), .alu .add .eax (.imm (BitVec.ofNat 32 smpSt)), .mov .ecx (.imm 168),
    .mov .edx (.imm 34), .mov .ebx (.imm 0x1f), .mov .edi (.reg .esi),
    .alu .add .edi (.imm (BitVec.ofNat 32 smpWk))]

/-- `squeeze(state, 168, 0, scratch, 840, work)`'s arguments. -/
def smpSqueezeArgs : List Instr :=
  [.mov .eax (.reg .esi), .alu .add .eax (.imm (BitVec.ofNat 32 smpSt)), .mov .ecx (.imm 168),
    .mov .edx (.imm 0), .mov .ebx (.reg .esi), .mov .ebp (.imm 840), .mov .edi (.reg .esi),
    .alu .add .edi (.imm (BitVec.ofNat 32 smpWk))]

/-- The candidates of the chunk at `esi`: `d₁` in `eax`, `d₂` in `ebx`; then compare the
coefficients accepted with 256. -/
def smpChunk : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .edx (at_ .esi 1), .mov .ebx (.reg .edx), .alu .and .edx (.imm 15),
    .shift .ror .edx 24, .alu .add .eax (.reg .edx), .shift .shr .ebx 4, .movzx8 .edx (at_ .esi 2),
    .shift .ror .edx 28, .alu .add .ebx (.reg .edx), .alu .cmp .ecx (.imm 256)]

/-- Accept the candidate in `r` if it is less than `q`: store it and count it. -/
def smpAccept (r : Reg) : Prog isa :=
  .seq (.block [.alu .cmp r (.imm Q)])
    (.ite .b (.block [.store (at_ .edi 0) r, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) (.block []))

/-- One iteration: nothing once there are 256 coefficients. -/
def smpBody : Prog isa :=
  .seq (.block smpChunk) <|
  .seq (.ite .b (.seq (smpAccept .eax) (.seq (.block [.alu .cmp .ecx (.imm 256)])
    (.ite .b (smpAccept .ebx) (.block [])))) (.block []))
    (.block [.alu .add .esi (.imm 3), .alu .sub .ebp (.imm 1)])

/-- `esi = scratch`, `edi = a`, `ecx = 0`, `ebp = 280`. -/
def smpLoopInit : List Instr :=
  [.mov .edi (.mem (at_ .esp 24)), .mov .ecx (.imm 0), .mov .ebp (.imm 280)]

/-- 1 if there are 256 coefficients, 0 otherwise. -/
def smpEnd : List Instr := [.mov .eax (.reg .ecx), .shift .shr .eax 8]

def sampleNTT : Prog isa :=
  leaf <|
  .seq (.block [.mov .esi (.mem (at_ .esp 28))]) <|
  .seq (zeroSt smpSt) <|
  .seq (.block smpAbsorbArgs) <|
  .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) <|
  .seq (.block smpPadArgs) <|
  .seq (callWith [.edi, .ebx, .edx, .ecx, .eax] "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) <|
  .seq (.block smpSqueezeArgs) <|
  .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze) <|
  .seq (.block smpLoopInit) <|
  .seq (.loop smpBody .ne) (.block smpEnd)

end VG.Impl.MlKem.X86
