import VerifiedGarbage.Impl.Pbkdf2.Stream.Arm
import VerifiedGarbage.Impl.MdStream.Arm

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function: 32-bit ARM implementation

The design of x86-64 and AArch64 (`Impl/Pbkdf2/Md/X86_64.lean`,
`Impl/Pbkdf2/Md/AArch64.lean`): one implementation of HMAC's `init` and
`finalize` and of PBKDF2's iteration for every Merkle–Damgård hash function
(MD5, SHA-1, SHA-224, SHA-256 and the SHA-512 family), calling its
compression function directly on blocks laid out at fixed offsets. A `Hash`
is what the code needs of one of them: its streaming functions as the code
calls them (`st`, `Impl/Pbkdf2/Stream/Arm.lean`, with the
block size `B`, the digest size `D` and their working space), the size `N`
of its hash value and `L` of its length field and the byte order of the
latter, the code writing its digest, and its compression function.

* `init(inner = r0, outer = r1, key = r2, key_len = r3, scratch = [sp])`,
  for a key of at most a block, sets both states' hash values with the
  streaming `init`, and makes each absorb its block with one compression, in
  its own buffer: `K₀ ⊕ ipad` is written into the inner state's buffer as
  words of `0x36` in every byte, then the key's bytes XORed in with a byte
  loop over the key alone (its length is public); `K₀ ⊕ opad` is that block
  XORed with `0x6a` in every byte (`ipad ⊕ opad`), word by word, into the
  outer state's buffer.
* `finalize(inner = r0, outer = r1, count = r2:r3, out = [sp],
  scratch = [sp, #4])` finalizes the inner state with the hash function's
  streaming `finalize`, into the block (its message has a length only known
  at run time). The outer state has absorbed one block, `K₀ ⊕ opad`, so the
  outer hash is one compression: of the outer state's hash value, copied to
  the hash value being compressed, with the block holding the inner digest
  and the padding of a `B + D`-byte message (`0x80`, zeros and the length
  field), written word by word at fixed offsets. The digest of the result
  goes to `out` (through the block for a truncated hash function, whose `N`
  bytes of digest `out` cannot hold).
* `iterate(key = r0, u = r1, n = r2, t = r3, scratch = [sp])` runs `n` steps
  `U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
  whose inner and outer streaming states are at `key` and `key + N + B`: each
  step is two compressions of a block that is `D` bytes of message followed
  by the padding of a `B + D`-byte message, the inner hash value with the
  block `U ‖ pad`, then the outer one with the block `digest ‖ pad`. The
  padding is written once, before the loop; the digest's `N - D` bytes past
  `D` (for a truncated hash function), which overwrite its start, are
  written back after each compression. `T ⊕= U` is word by word, in `t`.

`scratch` holds the working space of the functions we call (`8 W` bytes, the
streaming functions' and the compression function's), then our caller's
`r4`–`r11` and our return address, which each call replaces
(`Impl.Pbkdf2.Stream.Arm.Hash.saved`), then `finalize`'s and `iterate`'s hash
value being compressed (`N` bytes, at `hvO`) and right after it the block (`B`
bytes, at `blkO`); `init` compresses in the states. The compression function
is called with the hash value at `r0`, the block at `r1` (copied from `r6`),
one block in `r2` and `scratch` in `r3`; it never writes `r0` or `r3` and
preserves `r4`–`r11`, so our variables live there: `r11` is `scratch`, `r6`
the block, and, in `iterate`, `r4` = `key`, `r5` = the steps left and `r7` =
`t`; in `finalize`, `r5` = `outer` and `r7` = `out`. `r1`, `r9`, `r10` and
`r12` are temporaries (`init`'s registers are listed with its code). `init`
and `iterate` use no stack; `finalize` pushes the streaming `finalize`'s two
stack arguments around its call (`push {r1, r12}`), 8 bytes. Every address and
branch depends only on the pointers, `key_len` and `n`.
-/

namespace VG.Impl.Pbkdf2.Md.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (scrAt)
open VG.Impl.MdStream.Arm (compressAt)

/-- A Merkle–Damgård hash function's 32-bit ARM functions, as HMAC and
PBKDF2 call them. -/
structure Hash where
  /-- The streaming functions, as HMAC's `init` and `finalize` call them: the
  block size `B`, the sizes of the streaming state and of the digest `D`,
  the words of working space `W` of `update` and `finalize` (which the
  layout of `scratch` starts with), and the functions. -/
  st : Impl.Pbkdf2.Stream.Arm.Hash
  /-- The size of the hash value. -/
  N : Nat
  /-- The size of the length field. -/
  L : Nat
  /-- The length field is big-endian (little-endian otherwise). -/
  be : Bool
  /-- The size of the compression function's scratch space (at most `8 W`). -/
  so : Nat
  /-- Writes the digest of the hash value at `r0` to `r6` (`N` bytes);
  writes only `r9` and `r10`. -/
  out : List Instr
  /-- The compression function, and its name. -/
  compN : String
  compC : Prog isa

/-- Copying 32-bit word `k` from `[src + o₁]` to `[dst + o₂]`, through `r12`. -/
def cp (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.ldr .r12 src (o₁ + 4 * k), .str .r12 dst (o₂ + 4 * k)]

/-- `n` 32-bit words from `[src + o₁]` to `[dst + o₂]`. -/
def copyW (src dst : Reg) (o₁ o₂ n : Nat) : List Instr := (List.range n).flatMap (cp src dst o₁ o₂)

/-- `0x80` then zeros in the block at `r6`, from byte `a` up to byte `b`
(`a < b`, both multiples of 4). -/
def padFrom (a b : Nat) : List Instr :=
  [.mov .r12 (.imm 0x80), .str .r12 .r6 a, .mov .r12 (.imm 0)] ++
    (List.range ((b - a) / 4 - 1)).map fun k => .str .r12 .r6 (a + 4 + 4 * k)

/-- The constant words `ws`, stored at `[r6 + o]`, `[r6 + o + 4]`, … -/
def constW : Nat → List (BitVec 32) → List Instr
  | _, [] => []
  | o, w :: ws => [.movw .r12 (w.extractLsb' 0 16), .movt .r12 (w.extractLsb' 16 16), .str .r12 .r6 o] ++
      constW (o + 4) ws

/-- The words of the `L`-byte length field of an `n`-byte message (its length
in bits, `8 n`), big-endian if `be`, as stored, each little-endian. -/
def lenWords (be : Bool) (L n : Nat) : List (BitVec 32) :=
  (List.range (L / 4)).map fun j =>
    if be then rev (BitVec.ofNat 32 (8 * n / 2 ^ (32 * (L / 4 - 1 - j))))
    else BitVec.ofNat 32 (8 * n / 2 ^ (32 * j))

/-- `T ← T ⊕ U` for 32-bit word `k`, with `U` the block's first `D` bytes (at
`r6`) and `T` at `r7`. -/
def xorW (k : Nat) : List Instr :=
  [.ldr .r12 .r6 (4 * k), .ldr .r1 .r7 (4 * k), .dp .eor .r12 .r12 (.reg .r1), .str .r12 .r7 (4 * k)]

namespace Hash

variable (H : Hash)

/-- The block size and the size of the digest. -/
abbrev B : Nat := H.st.B
abbrev D : Nat := H.st.D

/-- Where the hash value being compressed is in `scratch`. -/
def hvO : Nat := H.st.buf

/-- Where the block is. -/
def blkO : Nat := H.st.buf + H.N

/-- The padding of a `B + D`-byte message after its `D` bytes in the block:
`0x80`, zeros, and the length field. -/
def pad : List Instr := padFrom H.D (H.B - H.L) ++ constW (H.B - H.L) (lenWords H.be H.L (H.B + H.D))

/-- The digest of the hash value into the block, and the padding it
overwrote written back. -/
def digest : List Instr := H.out ++ (if H.D < H.N then padFrom H.D H.N else [])

/-- One compression of the block into the hash value. -/
def compressBlock : Prog isa := .seq (.block [.mov .r1 (.reg .r6)]) (compressAt H.compN H.compC)

/-- `r0` at the hash value and `r6` at the block. -/
def atHv : List Instr := scrAt .r0 H.hvO ++ scrAt .r6 H.blkO

/-! ## HMAC's `init`

Registers: `r4` = `inner`, `r5` = `outer`, `r11` = `scratch`; in the key
loop, `r6` = the next key byte, `r8` + `N` = where it goes, `r7` = the bytes
left; for each compression, `r0` = the state, `r6` = its buffer and `r3` =
`scratch`. -/

/-- Saving our caller's registers and our return address, and setting up
ours. -/
def initPrologue : List Instr :=
  [.ldrSp .r12 0] ++ H.st.save ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
    .mov .r7 (.reg .r3), .mov .r11 (.reg .r12)]

/-- `ipad` in every byte of the inner state's buffer, a word at a time; then
the flags of `key_len = 0`, which skip the key loop for an empty key. -/
def fillIpad : List Instr :=
  [.movw .r1 0x3636, .movt .r1 0x3636] ++ (List.range (H.B / 4)).map (fun k => .str .r1 .r4 (H.N + 4 * k)) ++
    [.mov .r8 (.reg .r4), .cmp .r7 (.imm 0)]

/-- The key bytes, XORed with `ipad`, over the start of the buffer. -/
def keyLoop : Prog isa :=
  .loop (.block [.ldrb .r12 .r6 0, .dp .eor .r12 .r12 (.imm 0x36), .strb .r12 .r8 H.N,
    .dp .add .r6 .r6 (.imm 1), .dp .add .r8 .r8 (.imm 1), .subs .r7 .r7 (.imm 1)]) .ne

/-- Word `k` of the outer state's buffer, from the inner one's (`r1` =
`0x6a6a6a6a`): `K₀ ⊕ opad = (K₀ ⊕ ipad) ⊕ (ipad ⊕ opad)`. -/
def opadW (k : Nat) : List Instr :=
  [.ldr .r12 .r4 (H.N + 4 * k), .dp .eor .r12 .r12 (.reg .r1), .str .r12 .r5 (H.N + 4 * k)]

/-- The outer state's buffer, and the inner state's compression set up. -/
def fillOpad : List Instr :=
  [.movw .r1 0x6a6a, .movt .r1 0x6a6a] ++ (List.range (H.B / 4)).flatMap H.opadW ++
    [.mov .r0 (.reg .r4), .dp .add .r6 .r4 (.imm (BitVec.ofNat 32 H.N)), .mov .r3 (.reg .r11)]

/-- The two blocks: `K₀ ⊕ ipad` in the inner state's buffer and `K₀ ⊕ opad`
in the outer one's, the part of `init` between the calls of the streaming
`init` and the compressions. -/
def blocks : Prog isa :=
  .seq (.block H.fillIpad) (.seq (.ite .eq (.block []) H.keyLoop) (.block H.fillOpad))

/-- The outer state's compression set up (`r3` is still `scratch`). -/
def toOuter : List Instr := [.mov .r0 (.reg .r5), .dp .add .r6 .r5 (.imm (BitVec.ofNat 32 H.N))]

/-- HMAC's `init`: the streaming `init` of both states, then each state's
block compressed into its hash value. -/
def hmacInit : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (H.st.callInit .r4)
  (.seq (H.st.callInit .r5)
  (.seq H.blocks
  (.seq H.compressBlock
  (.seq (.block H.toOuter)
  (.seq H.compressBlock
    (.block H.st.restore)))))))

/-! ## HMAC's `finalize` -/

/-- Saving our caller's registers, with `outer` in `r5`, `out` in `r7` and
`scratch` in `r11`. -/
def finPrologue : List Instr :=
  [.ldrSp .r12 4] ++ H.st.save ++ [.mov .r5 (.reg .r1), .ldrSp .r7 0, .mov .r11 (.reg .r12)]

/-- The outer hash value, the padding after the inner digest in the block
and `scratch` in `r3`. -/
def finMid : List Instr := [.mov .r3 (.reg .r11)] ++ H.atHv ++ copyW .r5 .r0 0 0 (H.N / 4) ++ H.pad

/-- The MAC to `out` (through the block, if the digest is truncated), and
our caller's registers back. -/
def finOut : List Instr :=
  (if H.D < H.N then H.out ++ copyW .r6 .r7 0 0 (H.D / 4) else .mov .r6 (.reg .r7) :: H.out) ++ H.st.restore

def hmacFin : Prog isa :=
  .seq (.block H.finPrologue)
  (.seq (H.st.callFin [] [] H.blkO)
  (.seq (.block H.finMid)
  (.seq H.compressBlock
    (.block H.finOut))))

/-! ## `iterate` -/

/-- The hash value at `key + o` into the hash value being compressed. -/
def loadKey (o : Nat) : List Instr := copyW .r4 .r0 o 0 (H.N / 4)

/-- One step. -/
def body : Prog isa :=
  .seq (.block (H.loadKey 0))
  (.seq H.compressBlock
  (.seq (.block (H.digest ++ H.loadKey (H.N + H.B)))
  (.seq H.compressBlock
    (.block (H.digest ++ (List.range (H.D / 4)).flatMap xorW ++ [.subs .r5 .r5 (.imm 1)])))))

/-- Saving our caller's registers and our return address, setting up our
registers, and writing `U` and the padding into the block. -/
def prologue : List Instr :=
  [.ldrSp .r12 0] ++ H.st.save ++
    [.mov .r11 (.reg .r12), .mov .r7 (.reg .r3), .mov .r3 (.reg .r12), .mov .r4 (.reg .r0),
      .mov .r5 (.reg .r2)] ++ H.atHv ++ copyW .r1 .r6 0 0 (H.D / 4) ++ H.pad ++ [.cmp .r5 (.imm 0)]

def iterate : Prog isa :=
  .seq (.block H.prologue)
  (.seq (.ite .eq (.block []) (.loop H.body .ne))
    (.block H.st.restore))

end Hash

end VG.Impl.Pbkdf2.Md.Arm
