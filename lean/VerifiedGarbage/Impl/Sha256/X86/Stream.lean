import VerifiedGarbage.Impl.Sha256.X86

/-!
# Streaming SHA-256: x86 (32-bit) implementation

The streaming state (96 bytes at `state`) is the hash value followed by a
64-byte buffer (see `VG.Spec.Sha256.Repr`). Every argument is on the stack
(cdecl).

* `init(state)` stores `H⁽⁰⁾`.
* `update(state, count, data, len, scratch)` processes one block per
  iteration: straight from `data` while the buffer is empty and a whole block
  remains, otherwise by copying bytes into the buffer, compressing it once it
  is full.
* `finalize(state, count, out, scratch)` pads the buffered bytes (one or two
  blocks), compresses them and writes the digest.

The compression function's code (`Impl.Sha256.X86.compress`) is inlined. It
reads its arguments `(state, blocks, n, scratch)` from `[esp + 4 .. 20)`, so
before each compression we write them there, over our own arguments (the
callee owns them; see `VG.Spec.Sha256.updateX86`). It saves and restores
`ebx`, `esi`, `edi`, `ebp`, so our own variables live there across it, and
our caller's values of those registers are saved in `scratch[112..128)`.
Every address and branch depends only on the pointers, `count` and `len`.
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

/-- Compress the block at `eax`, with `[esp + 4]` and `[esp + 16]` already
holding the hash value's and the scratch space's addresses. -/
def compressAt : Prog isa :=
  .seq (.block [.store (at_ .esp 8) .eax, .mov .ecx (.imm 1), .store (at_ .esp 12) .ecx]) compress

/-! ## `update`

Registers: `ebx` = `state`, `ebp` = `data`, `esi` = bytes of `data` left,
`edi` = bytes in the buffer; within an iteration, `edx` = `scratch`, `eax` =
the block to compress and `ecx` = whether to compress it. The argument slots
hold `state` (`[esp + 4]`) and `scratch` (`[esp + 16]`). -/

/-- A whole block straight from `data`. -/
def direct : List Instr :=
  [.mov .edx (.mem (at_ .esp 16)), .mov .eax (.reg .ebp), .alu .add .ebp (.imm 64),
   .alu .sub .esi (.imm 64), .mov .ecx (.imm 1)]

/-- Copy `min(64 - edi, esi)` bytes of `data` into the buffer; if that fills it,
compress it. -/
def fill : Prog isa :=
  .seq (.block [.mov .edx (.mem (at_ .esp 16)), .mov .eax (.imm 64), .alu .sub .eax (.reg .edi),
      .alu .cmp .esi (.reg .eax)])
  (.seq (.ite .b (.block [.mov .eax (.reg .esi)]) (.block []))
  (.seq (.block [.alu .sub .esi (.reg .eax), .alu .add .edi (.reg .ebx), .alu .test .eax (.reg .eax)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi 32) .cl,
        .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne))
  (.seq (.block [.alu .sub .edi (.reg .ebx), .mov .ecx (.imm 0), .alu .cmp .edi (.imm 64)])
    (.ite .e (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 32), .mov .edi (.imm 0),
        .mov .ecx (.imm 1)]) (.block []))))))

def updateBody : Prog isa :=
  .seq (.block [.alu .test .edi (.reg .edi)])
  (.seq (.ite .e (.seq (.block [.alu .cmp .esi (.imm 64)]) (.ite .ae (.block direct) fill)) fill)
  (.seq (.block [.store (at_ .esp 4) .ebx, .store (at_ .esp 16) .edx, .alu .test .ecx (.reg .ecx)])
    (.ite .ne (.seq compressAt (.block [.mov .ecx (.imm 1), .alu .test .ecx (.reg .ecx)]))
      (.block []))))

def update : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 24))] ++ save .eax ++
      [.mov .ebx (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 16)), .mov .esi (.mem (at_ .esp 20)),
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 63),
       .store (at_ .esp 4) .ebx, .store (at_ .esp 16) .eax]))
    (.seq (.loop updateBody .ne) (.block (.mov .eax (.mem (at_ .esp 16)) :: restore .eax)))

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
  (.seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 32),
      .store (at_ .esp 4) .ebx, .store (at_ .esp 16) .ebp])
  (.seq compressAt
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
