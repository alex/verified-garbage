import VerifiedGarbage.Impl.Sha512.X86

/-!
# Streaming SHA-512: x86 (32-bit) implementation

The streaming state (192 bytes at `state`) is the hash value followed by a
128-byte buffer (see `VG.Spec.Sha512.Repr`); each 64-bit word of the hash
value is stored little-endian, so as its low half followed by its high half.
Every argument is on the stack (cdecl).

* `init iv (state)` stores the initial hash value `iv`.
* `update(state, count, data, len, scratch)` processes the data in pieces:
  each iteration copies as many bytes as fit into the buffer, and compresses
  the buffer once it is full.
* `finalize(state, count, out, scratch)` pads the buffered bytes (one or two
  blocks), compresses them and writes the final hash value.

The buffer is compressed by calling `vg_sha512_compress`, with
`scratch[0..224)` as its scratch space. Each call pushes the four arguments
(`scratch`, `1`, the buffer and `state`) in a frame of its own, popped (into
`eax`) when it returns: with the return address the call stores, it uses the
20 bytes below `esp`. The compression function preserves `ebx`, `esi`,
`edi` and `ebp`, so our variables live there across it, and our caller's
values of those registers are saved in `scratch[224..240)`; `scratch` and
`count` are read from their argument slots when needed. Byte `r` of the
buffer is addressed as `[eax + 64]` with `eax = state + r` computed just
before the access. Every address and branch depends only on `esp`, the
pointers, `count` and `len`.
-/

namespace VG.Impl.Sha512.X86.Stream

open VG.X86
open VG.Impl.Sha512.X86 (at_ compress lo hi)

/-- Store word `k` of `iv`, at `eax`. -/
def initW (iv : Spec.Sha512.HashValue) (k : Nat) : List Instr :=
  [.mov .ecx (.imm (lo iv[k]!)), .store (at_ .eax (8 * k)) .ecx,
   .mov .ecx (.imm (hi iv[k]!)), .store (at_ .eax (8 * k + 4)) .ecx]

def init (iv : Spec.Sha512.HashValue) : Prog isa :=
  .block (.mov .eax (.mem (at_ .esp 4)) :: (List.range 8).flatMap (initW iv))

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.ebx, 224), (.esi, 228), (.edi, 232), (.ebp, 236)]

/-- Save them, with `scratch` in `eax`. -/
def save : List Instr := saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restore them, with `scratch` in `eax`. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- A call of `vg_sha512_compress(ebx, eax, ecx, edx)`: its arguments pushed
last to first. -/
def compressCall : Prog isa :=
  .frame (.push [.edx, .ecx, .eax, .ebx]) (.call "vg_sha512_compress" compress) (.pop .eax 4)

/-- Compress the buffer of the state at `ebx` into its hash value, with the
scratch space whose address is at `[esp + d]`. -/
def compressAt (d : Nat) : Prog isa :=
  .seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm 64), .mov .ecx (.imm 1),
    .mov .edx (.mem (at_ .esp d))]) compressCall

/-! ## `update`

Registers: `ebx` = `state`, `esi` = `data`, `ebp` = bytes of `data` left,
`edi` = bytes in the buffer (`r`); `scratch` is at `[esp + 24]`. The loop
runs while `ebp ≠ 0`, so each iteration starts with `ebp ≥ 1` and `edi <
128`. -/

/-- Copy `ecx = min(128 - r, len) ≥ 1` bytes of `data` into the buffer; if
that fills it, compress it. -/
def fill : Prog isa :=
  .seq (.block [.mov .ecx (.imm 128), .alu .sub .ecx (.reg .edi), .alu .cmp .ebp (.reg .ecx)])
  (.seq (.ite .b (.block [.mov .ecx (.reg .ebp)]) (.block []))
  (.seq (.block [.alu .sub .ebp (.reg .ecx)])
  (.seq (.loop (.block [.movzx8 .edx (at_ .esi 0), .mov .eax (.reg .ebx), .alu .add .eax (.reg .edi),
      .store8 (at_ .eax 64) .dl, .alu .add .esi (.imm 1), .alu .add .edi (.imm 1),
      .alu .sub .ecx (.imm 1)]) .ne)
  -- Full: compress the buffer.
  (.seq (.block [.alu .cmp .edi (.imm 128)])
    (.ite .e (.seq (compressAt 24) (.block [.mov .edi (.imm 0)])) (.block []))))))

def updateBody : Prog isa := .seq fill (.block [.alu .test .ebp (.reg .ebp)])

def update : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 24))] ++ save ++
      [.mov .ebx (.mem (at_ .esp 4)), .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 127),
       .mov .esi (.mem (at_ .esp 16)), .mov .ebp (.mem (at_ .esp 20)), .alu .test .ebp (.reg .ebp)]))
  (.seq (.ite .e (.block []) (.loop updateBody .ne))
    (.block (.mov .eax (.mem (at_ .esp 24)) :: restore)))

/-! ## `finalize`

Registers: `ebx` = `state`, `edi` = bytes in the buffer (`r`), `esi` = 1
while the block being padded is not the last one (then 0); `count` is at
`[esp + 8]`, `out` at `[esp + 16]` and `scratch` at `[esp + 20]`. -/

/-- The message length in bits as a 128-bit big-endian integer, at the end of
the buffer: `count >> 61`, then `count << 3` (modulo 2⁶⁴). -/
def lenW : List Instr :=
  [.mov .eax (.mem (at_ .esp 8)), .mov .ecx (.mem (at_ .esp 12)),
   .mov .edx (.imm 0), .store (at_ .ebx 176) .edx,
   .mov .edx (.reg .ecx), .shift .shr .edx 29, .bswap .edx, .store (at_ .ebx 180) .edx,
   .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
   .mov .edx (.reg .eax), .shift .shr .edx 29, .alu .or .ecx (.reg .edx), .bswap .ecx,
   .store (at_ .ebx 184) .ecx,
   .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .bswap .eax,
   .store (at_ .ebx 188) .eax]

def finalizeBody : Prog isa :=
  -- Zero the buffer from `r` to 128, or to 112 in the last block.
  .seq (.block [.mov .eax (.imm 128), .alu .test .esi (.reg .esi)])
  (.seq (.ite .e (.block [.mov .eax (.imm 112)]) (.block []))
  (.seq (.block [.mov .ecx (.imm 0), .alu .sub .eax (.reg .edi)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx 64) .cl,
        .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne))
  -- In the last block, the message length.
  (.seq (.block [.alu .test .esi (.reg .esi)])
  (.seq (.ite .e (.block lenW) (.block []))
  (.seq (compressAt 20)
    (.block [.mov .edi (.imm 0), .alu .sub .esi (.imm 1)])))))))

/-- Word `k` of the final hash value, big-endian, to `out` at `eax`. -/
def outW (k : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .ebx (8 * k))), .mov .edx (.mem (at_ .ebx (8 * k + 4))), .bswap .edx,
   .bswap .ecx, .store (at_ .eax (8 * k)) .edx, .store (at_ .eax (8 * k + 4)) .ecx]

def finalize : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 20))] ++ save ++
      [.mov .ebx (.mem (at_ .esp 4)), .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm 127),
       -- The `0x80` byte.
       .mov .eax (.reg .ebx), .alu .add .eax (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .eax 64) .cl, .alu .add .edi (.imm 1),
       -- Two blocks if that leaves fewer than 16 bytes for the length (r ≥ 113).
       .mov .esi (.imm 0), .alu .cmp .edi (.imm 113)]))
  (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
  (.seq (.loop finalizeBody .e)
    (.block (.mov .eax (.mem (at_ .esp 16)) :: (List.range 8).flatMap outW ++
      .mov .eax (.mem (at_ .esp 20)) :: restore))))

end VG.Impl.Sha512.X86.Stream
