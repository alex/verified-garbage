import VerifiedGarbage.Impl.Sha256.X86
import VerifiedGarbage.Impl.MdStream.X86

/-!
# Streaming SHA-256: x86 (32-bit) implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`). Every argument is on the stack
(cdecl).

* `init(state)` stores `H⁽⁰⁾`.
* `update(state, count, data, len, scratch)` is the generic streaming code
  (`Impl/MdStream/X86.lean`): it compresses every whole block left in `data`
  with one call if the buffer is empty, and otherwise copies bytes into the
  buffer, compressing it once it is full.
* `finalize(state, count, out, scratch)` pads the buffered bytes (one or two
  blocks), compresses them and writes the digest.

The compression function is called (`vg_sha256_compress`,
`Impl.Sha256.X86.compress`) with `scratch[0..112)` as its scratch space.
Each call pushes its four arguments (`scratch`, the number of blocks, the
blocks and `state`) in a frame of its own, popped (into `eax`) when it
returns: with the return address the call stores, it uses the 20 bytes below
`esp`. The compression
function preserves `ebx`, `esi`, `edi` and `ebp`, so our variables live
there across it, and our caller's values of those registers are saved in
`scratch[112..128)`. Every address and branch depends only on `esp`, the
pointers, `count` and `len`.
-/

namespace VG.Impl.Sha256.X86.Stream

open VG.X86
open VG.Impl.Sha256.X86 (at_ compress)

def init : Prog isa :=
  .seq (.block [.mov .eax (.mem (at_ .esp 4))])
    (.block ((List.range 8).flatMap fun k =>
      [.mov .ecx (.imm Spec.Sha256.H0[k]!), .store (at_ .eax (4 * k)) .ecx]))

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.ebx, 112), (.esi, 116), (.edi, 120), (.ebp, 124)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store (at_ b d) r

/-- Restore them, with `scratch` in `b` (which must not be one of them). -/
def restore (b : Reg) : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ b d))

/-- Compress the block at `eax` into the hash value at `st`, with the scratch
space at `scr`: a call of `vg_sha256_compress(st, eax, 1, scr)`, its
arguments pushed last to first. -/
def compressAt (st scr : Reg) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 1)])
    (.frame (.push [scr, .ecx, .eax, st]) (.call "vg_sha256_compress" compress) (.pop .eax 4))

/-! ## `update`

The generic streaming code (`Impl/MdStream/X86.lean`). -/

/-- SHA-256's sizes, length field and digest in the generic streaming code. -/
def params : MdStream.X86.Params where
  N := 32
  so := 112
  len := MdStream.X86.len64 112 88 true
  out := MdStream.X86.out32 8 true

def update : Prog isa := MdStream.X86.update params "vg_sha256_compress" compress

/-! ## `finalize`

Registers: `ebx` = `state`, `ebp` = `scratch`, `edi` = bytes in the buffer,
`esi` = 1 while the block being padded is not the last one. `count` and `out`
are kept in `scratch[128..140)`. -/

/-- The message length in bits, big-endian, at `state[88..96)`. -/
def lengthStore : List Instr :=
  [.mov .eax (.mem (at_ .ebp 128)), .mov .ecx (.mem (at_ .ebp 132)),
   .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
   .mov .edx (.reg .eax), .shift .shr .edx 29, .alu .or .ecx (.reg .edx),
   .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .bswap .ecx, .store (at_ .ebx 88) .ecx, .bswap .eax, .store (at_ .ebx 92) .eax]

def finalizeBody : Prog isa :=
  -- Zero the buffer from `edi` to 64, or to 56 in the last block.
  .seq (.block [.mov .eax (.imm 64), .alu .test .esi (.reg .esi)])
  (.seq (.ite .e (.block [.mov .eax (.imm 56)]) (.block []))
  (.seq (.block [.mov .ecx (.imm 0), .alu .sub .eax (.reg .edi)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx 32) .cl,
        .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne))
  -- In the last block, the message length in bits, big-endian.
  (.seq (.block [.alu .test .esi (.reg .esi)])
  (.seq (.ite .e (.block lengthStore) (.block []))
  (.seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 32)])
  (.seq (compressAt .ebx .ebp)
    (.block [.mov .edi (.imm 0), .alu .sub .esi (.imm 1)]))))))))

def finalize : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 20))] ++ save .eax ++
      [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp 128) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp 132) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp 136) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       -- The `0x80` byte.
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx 32) .cl, .alu .add .edi (.imm 1),
       -- Two blocks if it leaves fewer than 8 bytes for the length.
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 57)]))
  (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
  (.seq (.loop finalizeBody .e)
    (.block (.mov .eax (.mem (at_ .ebp 136)) ::
      (List.range 8).flatMap (fun k =>
        [.mov .ecx (.mem (at_ .ebx (4 * k))), .bswap .ecx, .store (at_ .eax (4 * k)) .ecx]) ++
      [.mov .ebx (.mem (at_ .ebp 112)), .mov .esi (.mem (at_ .ebp 116)),
       .mov .edi (.mem (at_ .ebp 120)), .mov .ebp (.mem (at_ .ebp 124))]))))

end VG.Impl.Sha256.X86.Stream
