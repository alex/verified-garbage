import VerifiedGarbage.TCB.AArch64.Isa

/-!
# Streaming Merkle–Damgård hash functions: AArch64 implementation

The streaming `update` and `finalize` of MD5, SHA-1, SHA-256 and the SHA-512
family, which differ only in their sizes, in how they store the message
length and output the digest, and in the compression function they call
(`Params`). Each hash function's `Impl/<Alg>/AArch64/Stream.lean`
instantiates them.

The streaming state (`N + B` bytes at `state`) is the hash value (`N` bytes)
followed by a `B`-byte buffer.

* `update(state = x0, count = x1, data = x2, len = x3, scratch = x4)`
  compresses, in each iteration, every whole block left in `data` with one
  call if the buffer is empty (so that implementations that process several
  blocks at once can), and otherwise copies bytes into the buffer,
  compressing it once it is full.
* `finalize(state = x0, count = x1, out = x2, scratch = x3)` pads the
  buffered bytes (one or two blocks), compresses them and writes the digest.

`update` and `finalize` call the compression function (`name`, `code`) with
`scratch[0..so)` as its scratch space. It preserves `x19`–`x28`, so our own
variables live there (`x19` = `state`, `x20` = `scratch`), and our caller's
values of those registers are saved in `scratch[so..so+48)`. Our return
address (`x30`), which each call replaces, is saved in a stack frame around
the whole function.

The model has no register-offset addressing, so byte `r` of the buffer is
addressed as `[x12, #N]` with `x12 = state + r` computed just before the
access, and `data` is consumed through a pointer that advances. It has no
flags either: every comparison is a shift (`len ≥ B` iff `len >> log₂ B ≠ 0`)
or a subtraction tested with `cbz`/`cbnz`. Every address and branch depends
only on the pointers, `count` and `len`.
-/

namespace VG.Impl.MdStream.AArch64

open VG.AArch64

/-- `mov d, n` (as `add d, n, #0`). -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- What distinguishes one hash function's streaming code from another's. -/
structure Params where
  /-- The size of the hash value, where the buffer starts. -/
  N : Nat
  /-- The block size, a power of two. -/
  B : Nat
  /-- The size of the length field at the end of the last block. -/
  L : Nat
  /-- Where our caller's registers are saved in the scratch space, after the
  compression function's own. -/
  so : Nat
  /-- Stores the length field, from `count` in `x22`, at `x19 + N + B - L`;
  writes only `x9` and `x12`. -/
  len : List Instr
  /-- Writes the digest, from the hash value at `x19`, to `x21`; writes only
  `x9`. -/
  out : List Instr

variable (P : Params)

/-- `log₂ B`, the shift that divides by the block size. -/
def lg : Nat := Nat.log2 P.B

/-- The callee-saved registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.x19, P.so), (.x20, P.so + 8), (.x21, P.so + 16), (.x22, P.so + 24), (.x23, P.so + 32), (.x24, P.so + 40)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := (saved P).map fun (r, d) => .str .x r b d

/-- Restore them from `scratch` in `x20` (`x20`, the base, last). -/
def restore : List Instr :=
  [.ldr .x .x19 .x20 P.so, .ldr .x .x21 .x20 (P.so + 16), .ldr .x .x22 .x20 (P.so + 24),
    .ldr .x .x23 .x20 (P.so + 32), .ldr .x .x24 .x20 (P.so + 40), .ldr .x .x20 .x20 (P.so + 8)]

/-- Compress the blocks at `x1` into the hash value at `x19`, with scratch
space `x20`, by calling the compression function `name` (whose code is
`code`), after `n` sets their number in `x2`. -/
def compressWith (n : Instr) (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [mov .x0 .x19, n, mov .x3 .x20]) (.call name code)

/-- Compress one block. -/
def compressAt : String → Prog isa → Prog isa := compressWith (.movz .x .x2 1 0)

/-- Compress `x10` blocks. -/
def compressN : String → Prog isa → Prog isa := compressWith (mov .x2 .x10)

/-! ## `update`

Registers: `x21` = `data`, `x22` = bytes of `data` left, `x23` = bytes in the
buffer (`r`), `x10` = the number of blocks this iteration compresses (at
`x1`).
The loop runs while `x22 ≠ 0`, so each iteration starts with `x22 ≥ 1` and
`x23 < B`. -/

/-- Every whole block left, straight from `data`: `len >> log₂ B` blocks,
`(len >> log₂ B) << log₂ B` bytes. -/
def direct : List Instr :=
  [mov .x1 .x21, .lsr .x .x10 .x22 (lg P), .lsl .x .x9 .x10 (lg P), .add .x .x21 .x21 .x9,
    .sub .x .x22 .x22 .x9]

/-- The copy loop's body. -/
def copyBody : List Instr :=
  [.ldrb .x9 .x21 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 P.N, .addImm .x .x21 .x21 1,
    .addImm .x .x23 .x23 1, .subImm .x .x11 .x11 1]

/-- Copy `n = min(B - r, len) ≥ 1` bytes of `data` into the buffer; if that
fills it, compress it. -/
def fill : Prog isa :=
  -- x11 := B - r; if len < B and len + r < B (i.e. len < B - r), x11 := len.
  .seq (.block [.movz .x .x11 (BitVec.ofNat 16 P.B) 0, .sub .x .x11 .x11 .x23, .lsr .x .x9 .x22 (lg P)])
  (.seq (.ite (.zero .x .x9)
      (.seq (.block [.add .x .x9 .x22 .x23, .lsr .x .x9 .x9 (lg P)])
        (.ite (.zero .x .x9) (.block [mov .x11 .x22]) (.block [])))
      (.block []))
  (.seq (.block [.sub .x .x22 .x22 .x11])
  (.seq (.loop (.block (copyBody P)) (.nonzero .x .x11))
  -- Full: compress the buffer.
  (.seq (.block [.subImm .x .x9 .x23 P.B])
    (.ite (.zero .x .x9) (.block [.addImm .x .x1 .x19 P.N, .movz .x .x23 0 0, .movz .x .x10 1 0])
      (.block []))))))

def updateBody (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block [.movz .x .x10 0 0])
  (.seq (.ite (.zero .x .x23)
      (.seq (.block [.lsr .x .x9 .x22 (lg P)]) (.ite (.zero .x .x9) (fill P) (.block (direct P))))
      (fill P))
    (.ite (.zero .x .x10) (.block []) (compressN name code)))

/-- Save registers and set up ours. -/
def updateStart : List Instr :=
  save P .x4 ++ [mov .x19 .x0, mov .x20 .x4, mov .x21 .x2, mov .x22 .x3,
    .movz .x .x9 (BitVec.ofNat 16 (P.B - 1)) 0, .logic .and .x .x23 .x1 .x9]

/-- `update`, but for saving `x30`. -/
def updateMain (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (updateStart P))
  (.seq (.ite (.zero .x .x22) (.block []) (.loop (updateBody P name code) (.nonzero .x .x22)))
    (.block (restore P)))

def update (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push .x30) (updateMain P name code) (.pop .x30)

/-! ## `finalize`

Registers: `x21` = `out`, `x22` = `count`, `x23` = bytes in the buffer (`r`),
`x24` = 1 while the block being padded is not the last one (then 0). -/

/-- The zeroing loop's body. -/
def zeroBody : List Instr :=
  [.add .x .x12 .x19 .x23, .strb .x9 .x12 P.N, .addImm .x .x23 .x23 1, .subImm .x .x11 .x11 1]

def finalizeBody (name : String) (code : Prog isa) : Prog isa :=
  -- Zero the buffer from `r` to `B`, or to `B - L` in the last block.
  .seq (.block [.movz .x .x11 (BitVec.ofNat 16 P.B) 0])
  (.seq (.ite (.zero .x .x24) (.block [.movz .x .x11 (BitVec.ofNat 16 (P.B - P.L)) 0]) (.block []))
  (.seq (.block [.movz .x .x9 0 0, .sub .x .x11 .x11 .x23])
  (.seq (.ite (.zero .x .x11) (.block []) (.loop (.block (zeroBody P)) (.nonzero .x .x11)))
  -- In the last block, the length field.
  (.seq (.ite (.zero .x .x24) (.block P.len) (.block []))
  (.seq (.block [.addImm .x .x1 .x19 P.N])
  (.seq (compressAt name code)
    (.block [.movz .x .x23 0 0, .subImm .x .x24 .x24 1])))))))

/-- Save registers, append the `0x80` byte and choose the number of blocks. -/
def finalizeStart : List Instr :=
  save P .x3 ++ [mov .x19 .x0, mov .x20 .x3, mov .x21 .x2, mov .x22 .x1,
    .movz .x .x9 (BitVec.ofNat 16 (P.B - 1)) 0, .logic .and .x .x23 .x22 .x9,
    -- The `0x80` byte.
    .movz .x .x9 0x80 0, .add .x .x12 .x19 .x23, .strb .x9 .x12 P.N, .addImm .x .x23 .x23 1,
    -- Two blocks iff that leaves fewer than `L` bytes for the length (r > B - L).
    .addImm .x .x24 .x23 (P.L - 1), .lsr .x .x24 .x24 (lg P)]

/-- `finalize`, but for saving `x30`. -/
def finalizeMain (name : String) (code : Prog isa) : Prog isa :=
  .seq (.block (finalizeStart P))
  (.seq (.loop (finalizeBody P name code) (.zero .x .x24))
    (.block (P.out ++ restore P)))

def finalize (name : String) (code : Prog isa) : Prog isa :=
  .frame (.push .x30) (finalizeMain P name code) (.pop .x30)

/-! ## Length fields and digests

The `len` and `out` of the hash functions here. -/

/-- The length in bits, `8 · count` (modulo 2⁶⁴, from `count` in `x22`), as 8
bytes at `x19 + d`, big-endian if `be` and little-endian otherwise. An offset
that is not a multiple of 8 is addressed through `x12`. -/
def len64 (d : Nat) (be : Bool) : List Instr :=
  [.add .x .x9 .x22 .x22, .add .x .x9 .x9 .x9, .add .x .x9 .x9 .x9] ++
    (if be then [.rev .x9 .x9] else []) ++
    (if d % 8 = 0 then [.str .x .x9 .x19 d] else [.addImm .x .x12 .x19 d, .str .x .x9 .x12 0])

/-- The `n` 32-bit words at `x19`, written to `x21`, big-endian if `be` and
little-endian otherwise. -/
def out32 (n : Nat) (be : Bool) : List Instr :=
  (List.range n).flatMap fun k =>
    [.ldr .w .x9 .x19 (4 * k)] ++ (if be then [.rev32 .x9 .x9] else []) ++ [.str .w .x9 .x21 (4 * k)]

/-- The `n` 64-bit words at `x19`, written to `x21` big-endian. -/
def out64 (n : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.ldr .x .x9 .x19 (8 * k), .rev .x9 .x9, .str .x .x9 .x21 (8 * k)]

/-- The length in bits as a 16-byte big-endian integer at `x19 + d`:
`count >> 61`, then `8 · count` (modulo 2⁶⁴). `d` is a multiple of 8. -/
def len128 (d : Nat) : List Instr :=
  [.lsr .x .x9 .x22 61, .rev .x9 .x9, .str .x .x9 .x19 d] ++ len64 (d + 8) true

end VG.Impl.MdStream.AArch64
