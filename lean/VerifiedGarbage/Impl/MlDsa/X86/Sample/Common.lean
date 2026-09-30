import VerifiedGarbage.Impl.MlKem.X86.Sample

/-!
# ML-DSA on x86 (32-bit): sampling from SHAKE

The sampling functions `vg_mldsa_rej_ntt_poly`, `vg_mldsa_rej_bounded_poly`,
`vg_mldsa_expand_mask_poly` and `vg_mldsa_sample_in_ball` are leaves in the
sense of ML-KEM's `vg_mlkem_sample_ntt` (`Impl/MlKem/X86/Sample.lean`): each
saves its caller's `ebx`, `esi`, `edi` and `ebp` in a frame of 16 bytes
(`leaf`), and keeps `esi` = `scratch` across the calls of the Keccak
functions (which preserve it), each of which pushes its arguments in a frame
of its own (`callWith`). `scratch` (2048 bytes) holds, from byte 0, the
Keccak state (200 bytes), the Keccak functions' working space (640 bytes)
and, from byte 840, the XOF output.

`sponge iS rate len outlen` hashes the message whose pointer is the first
argument and whose length is `len` (an immediate, or the second argument):
it loads `scratch` (argument `iS`) into `esi`, zeroes the state (the empty
message), absorbs the message with `vg_keccak_absorb`, pads it with
`vg_keccak_pad` (SHAKE's suffix `0x1f`) from the position `len` (the
message is shorter than a block), and squeezes `outlen` bytes to
`scratch + 840` with `vg_keccak_squeeze`. Its addresses and branches depend
only on `esp`, the pointers and the length.
-/

namespace VG.Impl.MlDsa.X86.Sample

open VG.X86
open VG.Impl.MlKem.X86 (at_ callWith zeroSt)

/-- `q = 8380417`, as an immediate. -/
def qImm : BitVec 32 := 8380417

/-- Where the Keccak working space and the XOF output start in `scratch`. -/
abbrev wkOff : Nat := 200
abbrev outOff : Nat := 840

/-- `[esp + 20 + 4i]`: argument `i`, after the leaf's push. -/
def argOp (i : Nat) : MemOp := at_ .esp (20 + 4 * i)

/-- `absorb(scratch, rate, 0, msg, len, scratch + 200)`'s arguments. -/
def absArgs (rate : Nat) (len : Src) : List Instr :=
  [.mov .eax (.reg .esi), .mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0),
    .mov .ebx (.mem (argOp 0)), .mov .ebp len, .mov .edi (.reg .esi),
    .alu .add .edi (.imm (BitVec.ofNat 32 wkOff))]

/-- `pad(scratch, rate, len, 0x1f, scratch + 200)`'s arguments. -/
def padArgs (rate : Nat) (len : Src) : List Instr :=
  [.mov .eax (.reg .esi), .mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx len, .mov .ebx (.imm 0x1f),
    .mov .edi (.reg .esi), .alu .add .edi (.imm (BitVec.ofNat 32 wkOff))]

/-- `squeeze(scratch, rate, 0, scratch + 840, outlen, scratch + 200)`'s arguments. -/
def sqzArgs (rate outlen : Nat) : List Instr :=
  [.mov .eax (.reg .esi), .mov .ecx (.imm (BitVec.ofNat 32 rate)), .mov .edx (.imm 0), .mov .ebx (.reg .esi),
    .alu .add .ebx (.imm (BitVec.ofNat 32 outOff)), .mov .ebp (.imm (BitVec.ofNat 32 outlen)),
    .mov .edi (.reg .esi), .alu .add .edi (.imm (BitVec.ofNat 32 wkOff))]

/-- `outlen` bytes of SHAKE with the rate `rate` of the message at argument
0, of `len` bytes, to `scratch + 840`, with `esi` = `scratch` (argument
`iS`). -/
def sponge (iS rate : Nat) (len : Src) (outlen : Nat) : Prog isa :=
  .seq (.block [.mov .esi (.mem (argOp iS))]) <|
  .seq (zeroSt 0) <|
  .seq (.block (absArgs rate len)) <|
  .seq (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_absorb" Impl.Sha3.X86.Stream.absorb) <|
  .seq (.block (padArgs rate len)) <|
  .seq (callWith [.edi, .ebx, .edx, .ecx, .eax] "vg_keccak_pad" Impl.Sha3.X86.Stream.pad) <|
  .seq (.block (sqzArgs rate outlen))
    (callWith [.edi, .ebp, .ebx, .edx, .ecx, .eax] "vg_keccak_squeeze" Impl.Sha3.X86.Stream.squeeze)

/-- `eax ← r >> 8`: 1 if `r` = 256, 0 if it is less. -/
def retJ (r : Reg) : List Instr := [.mov .eax (.reg r), .shift .shr .eax 8]

end VG.Impl.MlDsa.X86.Sample
