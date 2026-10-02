import VerifiedGarbage.TCB.X86.Isa

/-!
# Streaming Merkle–Damgård hash functions: x86 (32-bit) implementation

The streaming `update` and `finalize` of MD5, SHA-1, SHA-256 and the SHA-512
family, which differ only in their sizes, in how they store the message
length and output the digest, and in the compression function they call
(`Params`). Each hash function's `Impl/<Alg>/X86/Stream.lean` instantiates
them. The same algorithm as on x86-64 (`VG.Impl.MdStream.X86_64`).

The streaming state (`N + B` bytes at `state`) is the hash value (`N` bytes)
followed by a `B`-byte buffer. Every argument is on the stack (cdecl).

* `update(state, count, data, len, scratch)` compresses, in each iteration,
  every whole block left in `data` with one call if the buffer is empty (so
  that implementations that process several blocks at once can), and
  otherwise copies bytes into the buffer, compressing it once it is full.
* `finalize(state, count, out, scratch)` pads the buffered bytes (one or two
  blocks), compresses them and writes the digest.

The compression function (`name`, `code`: `compress(state, blocks, n,
scratch)`) is called with `scratch[0..so)` as its scratch space. Each call
pushes its four arguments (`scratch`, `1`, the block and `state`) in a frame
of its own, popped (into `eax`) when it returns: with the return address the
call stores, it uses the 20 bytes below `esp`. The compression function
preserves `ebx`, `esi`, `edi` and `ebp`, so our variables live there across
it, and our caller's values of those registers are saved in
`scratch[so..so+16)`. Every address and branch depends only on `esp`, the
pointers, `count` and `len`.
-/

namespace VG.Impl.MdStream.X86

open VG.X86

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- What distinguishes one hash function's streaming code from another's. -/
structure Params where
  /-- The size of the hash value, where the buffer starts. -/
  N : Nat
  /-- The block size. -/
  B : Nat
  /-- The size of the length field at the end of the last block. -/
  L : Nat
  /-- Where our caller's registers are saved in the scratch space, after the
  compression function's own; `finalize` keeps `count` and `out` after them,
  in `scratch[so+16..so+28)`. -/
  so : Nat
  /-- Stores the length field, from `count` in `[ebp + so + 16]` (low word)
  and `[ebp + so + 20]` (high word), at `ebx + N + B - L`; writes only `eax`,
  `ecx` and `edx` (and the flags). -/
  len : List Instr
  /-- Writes the digest, from the hash value at `ebx`, to `eax`; writes only
  `ecx` (and the flags). -/
  out : List Instr

variable (P : Params)

/-- The callee-saved registers, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.ebx, P.so), (.esi, P.so + 4), (.edi, P.so + 8), (.ebp, P.so + 12)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := (saved P).map fun (r, d) => .store (at_ b d) r

/-- Restore them, with `scratch` in `b` (restored last if it is one of them). -/
def restore (b : Reg) : List Instr := (saved P).map fun (r, d) => .mov r (.mem (at_ b d))

/-- Compress the `ecx` blocks at `eax` into the hash value at `st`, with the
scratch space at `scr`, after `n` (which sets `ecx`): a call of
`compress(st, eax, ecx, scr)`, its arguments pushed last to first. -/
def compressWith (n : List Instr) (name : String) (code : Prog isa) (st scr : Reg) : Prog isa :=
  .seq (.block n) (.frame (.push [scr, .ecx, .eax, st]) (.call name code) (.pop .eax 4))

/-- Compress one block. -/
def compressAt : String → Prog isa → Reg → Reg → Prog isa := compressWith [.mov .ecx (.imm 1)]

/-- Compress `ecx` blocks. -/
def compressN : String → Prog isa → Reg → Reg → Prog isa := compressWith []

/-! ## `update`

Registers: `ebx` = `state`, `ebp` = `data`, `esi` = bytes of `data` left,
`edi` = bytes in the buffer; within an iteration, `eax` = the block to
compress and `ecx` = the number of blocks to compress there. `scratch` is read from its
argument slot (`[esp + 24]`) when needed. -/

/-- Every whole block left, straight from `data`: `esi - esi mod B` bytes,
`(esi - esi mod B) >> log₂ B` blocks. -/
def direct : List Instr :=
  [.mov .eax (.reg .ebp), .mov .ecx (.reg .esi), .alu .and .ecx (.imm (BitVec.ofNat 32 (P.B - 1))),
   .mov .edx (.reg .esi), .alu .sub .edx (.reg .ecx), .alu .add .ebp (.reg .edx), .mov .esi (.reg .ecx),
   .mov .ecx (.reg .edx), .shift .shr .ecx (Nat.log2 P.B)]

/-- Copy `min(B - edi, esi)` bytes of `data` into the buffer; if that fills it,
compress it. -/
def fill : Prog isa :=
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 P.B)), .alu .sub .eax (.reg .edi), .alu .cmp .esi (.reg .eax)])
  (.seq (.ite .b (.block [.mov .eax (.reg .esi)]) (.block []))
  (.seq (.block [.alu .sub .esi (.reg .eax), .alu .add .edi (.reg .ebx), .alu .test .eax (.reg .eax)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.movzx8 .ecx (at_ .ebp 0), .store8 (at_ .edi P.N) .cl,
        .alu .add .ebp (.imm 1), .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne))
  (.seq (.block [.alu .sub .edi (.reg .ebx), .mov .ecx (.imm 0), .alu .cmp .edi (.imm (BitVec.ofNat 32 P.B))])
    (.ite .e (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 P.N)), .mov .edi (.imm 0),
        .mov .ecx (.imm 1)]) (.block []))))))

def updateBody (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .edi (.reg .edi)])
  (.seq (.ite .e (.seq (.block [.alu .cmp .esi (.imm (BitVec.ofNat 32 P.B))]) (.ite .ae (.block (direct P)) (fill P)))
    (fill P))
  (.seq (.block [.alu .test .ecx (.reg .ecx)])
    (.ite .ne (.seq (.block [.mov .edx (.mem (at_ .esp 24))])
        (.seq (compressN name code .ebx .edx) (.block [.mov .ecx (.imm 1), .alu .test .ecx (.reg .ecx)])))
      (.block []))))

def update (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 24))] ++ save P .eax ++
      [.mov .ebx (.mem (at_ .esp 4)), .mov .ebp (.mem (at_ .esp 16)), .mov .esi (.mem (at_ .esp 20)),
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm (BitVec.ofNat 32 (P.B - 1)))]))
    (.seq (.loop (updateBody P name code) .ne) (.block (.mov .eax (.mem (at_ .esp 24)) :: restore P .eax)))

/-! ## `finalize`

Registers: `ebx` = `state`, `ebp` = `scratch`, `edi` = bytes in the buffer,
`esi` = 1 while the block being padded is not the last one. `count` and
`out` are kept in `scratch[so+16..so+28)`. -/

def finalizeBody (name : String) (code : Prog isa) : Prog isa :=
  -- Zero the buffer from `edi` to `B`, or to `B - L` in the last block.
  .seq (.block [.mov .eax (.imm (BitVec.ofNat 32 P.B)), .alu .test .esi (.reg .esi)])
  (.seq (.ite .e (.block [.mov .eax (.imm (BitVec.ofNat 32 (P.B - P.L)))]) (.block []))
  (.seq (.block [.mov .ecx (.imm 0), .alu .sub .eax (.reg .edi)])
  (.seq (.ite .e (.block [])
      (.loop (.block [.mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .store8 (at_ .edx P.N) .cl,
        .alu .add .edi (.imm 1), .alu .sub .eax (.imm 1)]) .ne))
  -- In the last block, the length field.
  (.seq (.block [.alu .test .esi (.reg .esi)])
  (.seq (.ite .e (.block P.len) (.block []))
  (.seq (.block [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 P.N))])
  (.seq (compressAt name code .ebx .ebp)
    (.block [.mov .edi (.imm 0), .alu .sub .esi (.imm 1)]))))))))

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block ([.mov .eax (.mem (at_ .esp 20))] ++ save P .eax ++
      [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
       .mov .ecx (.mem (at_ .esp 8)), .store (at_ .ebp (P.so + 16)) .ecx,
       .mov .ecx (.mem (at_ .esp 12)), .store (at_ .ebp (P.so + 20)) .ecx,
       .mov .ecx (.mem (at_ .esp 16)), .store (at_ .ebp (P.so + 24)) .ecx,
       .mov .edi (.mem (at_ .esp 8)), .alu .and .edi (.imm (BitVec.ofNat 32 (P.B - 1))),
       -- The `0x80` byte.
       .mov .edx (.reg .ebx), .alu .add .edx (.reg .edi), .mov .ecx (.imm 0x80),
       .store8 (at_ .edx P.N) .cl, .alu .add .edi (.imm 1),
       -- Two blocks if it leaves fewer than `L` bytes for the length.
       .mov .esi (.imm 0), .alu .cmp .edi (.imm (BitVec.ofNat 32 (P.B - P.L + 1)))]))
  (.seq (.ite .ae (.block [.mov .esi (.imm 1)]) (.block []))
  (.seq (.loop (finalizeBody P name code) .e)
    (.block (.mov .eax (.mem (at_ .ebp (P.so + 24))) :: (P.out ++ restore P .ebp)))))

/-! ## Length fields and digests

The `len` and `out` of the hash functions here. -/

/-- The length in bits, `8 · count` (modulo 2⁶⁴, from `count` in `eax` (low
word) and `ecx` (high word)), as 8 bytes at `ebx + d`, big-endian if `be` and
little-endian otherwise. -/
def len64Of (d : Nat) (be : Bool) : List Instr :=
  [.alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx), .alu .add .ecx (.reg .ecx),
   .mov .edx (.reg .eax), .shift .shr .edx 29, .alu .or .ecx (.reg .edx),
   .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax)] ++
  if be then [.bswap .ecx, .store (at_ .ebx d) .ecx, .bswap .eax, .store (at_ .ebx (d + 4)) .eax]
  else [.store (at_ .ebx d) .eax, .store (at_ .ebx (d + 4)) .ecx]

/-- Load `count`, from `[ebp + so + 16]` (low word) and `[ebp + so + 20]`
(high word), into `eax` and `ecx`. -/
def loadCount (so : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp (so + 16))), .mov .ecx (.mem (at_ .ebp (so + 20)))]

/-- `len64Of` from `count` in scratch. -/
def len64 (so d : Nat) (be : Bool) : List Instr := loadCount so ++ len64Of d be

/-- The `n` 32-bit words at `ebx`, written to `eax`, big-endian if `be` and
little-endian otherwise. -/
def out32 (n : Nat) (be : Bool) : List Instr :=
  (List.range n).flatMap fun k => [.mov .ecx (.mem (at_ .ebx (4 * k)))] ++
    (if be then [.bswap .ecx] else []) ++ [.store (at_ .eax (4 * k)) .ecx]

/-- The `n` 64-bit words at `ebx` (each little-endian: its low half first),
written to `eax` big-endian. -/
def out64 (n : Nat) : List Instr :=
  (List.range n).flatMap fun k =>
    [.mov .ecx (.mem (at_ .ebx (8 * k + 4))), .bswap .ecx, .store (at_ .eax (8 * k)) .ecx,
     .mov .ecx (.mem (at_ .ebx (8 * k))), .bswap .ecx, .store (at_ .eax (8 * k + 4)) .ecx]

end VG.Impl.MdStream.X86
