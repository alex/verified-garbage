import VerifiedGarbage.Impl.Hmac.Generic.X86
import VerifiedGarbage.Impl.MdStream.X86

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function: x86 (32-bit) implementation

One implementation of HMAC's `finalize` and of PBKDF2's iteration for every
hash function that x86 has streaming functions and a compression function
for, with blocks of 64 bytes (MD5, SHA-1, SHA-256: `Impl/MdStream/X86.lean`)
or 128 (the SHA-512 family: `Impl/Sha512/X86/Stream.lean`). A `Hash` is what the
code needs of one of them: its streaming functions, as HMAC's `init` calls
them (`Impl/Hmac/Generic/X86.lean`, with the sizes of the block, the state
and the digest), the size of its hash value and of its length field, the
byte order of the length field, the compression function (its name, code
and scratch space), and the code writing the digest of a hash value.

Both functions compress a block that is `D` bytes of message followed by the
padding of a `B + D`-byte message, into a hash value at `ebx` with the block
right after it, at `ebx + N` (a streaming state's layout):

* `iterate(key, u, n, t, scratch)` runs `n` steps `U ← HMAC (K₀, U)`,
  `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key whose inner and outer
  streaming states are at `key` and `key + S`. Those have each absorbed one
  block, so HMAC of the `D`-byte `U` is two compressions: the inner hash
  value with the block `U ‖ pad`, then the outer hash value with the block
  `digest ‖ pad`. The padding is written once, before the loop; the
  digest's `N - D` bytes past `D` (for a truncated hash function), which
  overwrite its start, are written back after each. `T ← T ⊕ U` is computed
  in `t` itself, word by word.
* `finalize(inner, outer, count, out, scratch)` finalizes the inner state
  into `scratch` with the hash function's streaming `finalize` (its
  message has a variable length). The outer hash, of the outer block and
  that digest, is then one compression: the inner state is no longer
  needed, so it gets the outer hash value and, in its buffer, the digest
  followed by the padding. The MAC is written to `out`: directly, or for a
  digest shorter than the hash value, into the buffer and its first `D`
  bytes copied.

`scratch` holds the compression function's scratch space (`[0..so)`, within
the working space of the streaming functions, `8 W` bytes), our caller's
`ebx`, `esi`, `edi` and `ebp` (`Impl.Hmac.Generic.X86.Hash.saved`), then our
buffers: `iterate`'s hash value and block, `finalize`'s digest. The
compression function is called as by the streaming functions, with its
arguments pushed in a frame of their own (`Impl.MdStream.X86.compressAt`),
using the 20 bytes below `esp`; it preserves `ebx`, `esi`, `edi` and `ebp`,
so our variables live there. Every copy and every write of the padding is a
32-bit word at a fixed offset. Every address and branch depends only on
`esp`, the pointers, `count` and `n`.
-/

namespace VG.Impl.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (at_)

/-- Word `k` from `[src + o₁]` to `[dst + o₂]`, through `ecx`. -/
def cpW (src dst : Reg) (o₁ o₂ k : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ src (o₁ + 4 * k))), .store (at_ dst (o₂ + 4 * k)) .ecx]

/-- `n` words from `[src + o₁]` to `[dst + o₂]`. -/
def copyW (src : Reg) (o₁ : Nat) (dst : Reg) (o₂ n : Nat) : List Instr :=
  (List.range n).flatMap (cpW src dst o₁ o₂)

/-- The little-endian 32-bit word of bytes `4 k … 4 k + 3` of `xs`. -/
def wordOf (xs : List Byte) (k : Nat) : BitVec 32 :=
  xs.getD (4 * k + 3) 0 ++ xs.getD (4 * k + 2) 0 ++ xs.getD (4 * k + 1) 0 ++ xs.getD (4 * k) 0

/-- The first `4 n` bytes of `xs` at `[dst + o]`, a word at a time through `ecx`. -/
def storeW (dst : Reg) (o : Nat) (xs : List Byte) (n : Nat) : List Instr :=
  (List.range n).flatMap fun k => [.mov .ecx (.imm (wordOf xs k)), .store (at_ dst (o + 4 * k)) .ecx]

/-- The end of the last block of a `B + D`-byte message, after its last `D`
bytes: `0x80`, zeros, and the `L`-byte length field, the length in bits,
big-endian if `be` and little-endian otherwise. -/
def tail (B D L : Nat) (be : Bool) : List Byte :=
  [0x80] ++ List.replicate (B - L - 1 - D) 0 ++
    (List.range L).map fun i => BitVec.ofNat 8 ((8 * (B + D)) >>> (8 * (if be then L - 1 - i else i)))

/-- A Merkle–Damgård hash function's x86 functions, as HMAC and PBKDF2 use
them. -/
structure Hash where
  /-- The streaming functions HMAC's `init` and `finalize` call, with the
  sizes of the block, the state and the digest. -/
  st : Impl.Hmac.Generic.X86.Hash
  /-- The size of the hash value (where a state's buffer starts). -/
  N : Nat
  /-- The size of the length field. -/
  L : Nat
  /-- Whether the length field is big-endian. -/
  be : Bool
  /-- The bytes of scratch space of the compression function. -/
  so : Nat
  /-- The compression function `compress(state, blocks, n, scratch)`, and its name. -/
  compN : String
  compC : Prog isa
  /-- Writes the digest of the `N`-byte hash value at `ebx` to `eax`; writes
  only `ecx` and `edx` (and the flags). -/
  out : List Instr

namespace Hash

variable (H : Hash)

/-- The block size, and the sizes of the state and of the digest. -/
abbrev B : Nat := H.st.B
abbrev S : Nat := H.st.S
abbrev D : Nat := H.st.D

/-- The end of the block after the digest. -/
def tailB : List Byte := tail H.B H.D H.L H.be

/-! ## The block after the hash value at `ebx` -/

/-- `eax ← ebx + N`: the block. -/
def atBlk : List Instr := [.mov .eax (.reg .ebx), .alu .add .eax (.imm (BitVec.ofNat 32 H.N))]

/-- The padding after the block's first `D` bytes. -/
def pad : List Instr := storeW .ebx (H.N + H.D) H.tailB ((H.B - H.D) / 4)

/-- The digest of the hash value into the block, and the padding it
overwrote (for a digest shorter than the hash value) written back. -/
def digest : List Instr := H.atBlk ++ H.out ++ storeW .ebx (H.N + H.D) H.tailB ((H.N - H.D) / 4)

/-- One compression of the block (at `eax`) into the hash value, with the
scratch space at `ebp`. -/
def cmp : Prog isa := Impl.MdStream.X86.compressAt H.compN H.compC .ebx .ebp

/-! ## `iterate`

Registers: `ebp` = `scratch`, `ebx` = the hash value being compressed (at
`scratch + buf`, the block right after it), `esi` = `key`, `edi` = the steps
left; `t` is read from the stack into `edx` for `T ← T ⊕ U`. -/

/-- The hash value at `key + o` into the one at `ebx`. -/
def loadKey (o : Nat) : List Instr := copyW .esi o .ebx 0 (H.N / 4)

/-- `T ← T ⊕ U` for word `k`, with `T` at `edx` and `U` the block's first `D` bytes. -/
def xorW (k : Nat) : List Instr :=
  [.mov .ecx (.mem (at_ .ebx (H.N + 4 * k))), .alu .xor .ecx (.mem (at_ .edx (4 * k))),
    .store (at_ .edx (4 * k)) .ecx]

/-- `t`, then `T ← T ⊕ U` and the count. -/
def tStep : List Instr :=
  [.mov .edx (.mem (at_ .esp 16))] ++ (List.range (H.D / 4)).flatMap H.xorW ++ [.alu .sub .edi (.imm 1)]

/-- One step. -/
def body : Prog isa :=
  .seq (.block (H.loadKey 0 ++ H.atBlk))
  (.seq H.cmp
  (.seq (.block (H.digest ++ H.loadKey H.S ++ H.atBlk))
  (.seq H.cmp
    (.block (H.digest ++ H.tStep)))))

/-- Saving our caller's registers, setting up ours, and writing `U` and the
padding into the block. -/
def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ H.st.save ++
    [.mov .ebp (.reg .eax), .mov .esi (.mem (at_ .esp 4)), .mov .edi (.mem (at_ .esp 12)),
      .mov .ebx (.reg .ebp), .alu .add .ebx (.imm (BitVec.ofNat 32 H.st.buf)), .mov .edx (.mem (at_ .esp 8))] ++
    copyW .edx 0 .ebx H.N (H.D / 4) ++ H.pad ++ [.alu .test .edi (.reg .edi)]

def iterate : Prog isa :=
  .seq (.block H.prologue)
  (.seq (.ite .e (.block []) (.loop H.body .ne))
    (.block H.st.restore))

/-! ## HMAC's `init`

Registers: `ebp` = `scratch`, `ebx` = `inner` (the hash value being
compressed: then `outer`), `esi` = `outer`; in the key loop, `edi` = the next
key byte, `edx` = where it goes, `ecx` = the bytes left. -/

/-- Saving our caller's registers, and `scratch`, `inner` and `outer` into
`ebp`, `ebx` and `esi`. -/
def initPrologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ H.st.save ++
    [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8))]

/-- `ipad` in every byte of the inner state's buffer, a word at a time;
then the key and its length (whose flags skip the key loop for an empty
key), and the start of the buffer. -/
def fillIpad : List Instr :=
  .mov .ecx (.imm 0x36363636) :: (List.range (H.B / 4)).map (fun k => .store (at_ .ebx (H.N + 4 * k)) .ecx) ++
    [.mov .edi (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 16)), .mov .edx (.reg .ebx),
      .alu .add .edx (.imm (BitVec.ofNat 32 H.N)), .alu .test .ecx (.reg .ecx)]

/-- The key bytes, XORed with `ipad`, over the start of the buffer. -/
def keyLoop : Prog isa :=
  .loop (.block [.movzx8 .eax (at_ .edi 0), .alu .xor .eax (.imm 0x36), .store8 (at_ .edx 0) .al,
    .alu .add .edi (.imm 1), .alu .add .edx (.imm 1), .alu .sub .ecx (.imm 1)]) .ne

/-- Word `k` of the outer state's buffer, from the inner one's:
`K₀ ⊕ opad = (K₀ ⊕ ipad) ⊕ (ipad ⊕ opad)`. -/
def opadW (k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebx (H.N + 4 * k))), .alu .xor .eax (.imm 0x6a6a6a6a),
    .store (at_ .esi (H.N + 4 * k)) .eax]

/-- The outer state's buffer, and `eax` at the inner one. -/
def fillOpad : List Instr := (List.range (H.B / 4)).flatMap H.opadW ++ H.atBlk

/-- The two blocks: `K₀ ⊕ ipad` in the inner state's buffer and `K₀ ⊕ opad`
in the outer one's, the part of `init` between the calls of the streaming
`init` and the compressions. -/
def blocks : Prog isa :=
  .seq (.block H.fillIpad) (.seq (.ite .e (.block []) keyLoop) (.block H.fillOpad))

/-- `ebx` at the outer state, and `eax` at its buffer. -/
def toOuter : List Instr := .mov .ebx (.reg .esi) :: H.atBlk

def hmacInit : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (H.st.callInit .ebx)
  (.seq (H.st.callInit .esi)
  (.seq H.blocks
  (.seq H.cmp
  (.seq (.block H.toOuter)
  (.seq H.cmp
    (.block H.st.restore)))))))

/-! ## HMAC's `finalize`

Registers as in the streaming-level design (`Impl.Hmac.Generic.X86.Hash.finPrologue`):
`ebx` = `inner`, `esi` = `outer`, `edi` = `out`, `ebp` = `scratch`. The
streaming `finalize` writes the inner digest to `scratch + buf`. -/

/-- The outer hash value over the inner state's, the inner digest into its
buffer and the padding after it, and `eax` at the buffer. -/
def finMid : List Instr :=
  copyW .esi 0 .ebx 0 (H.N / 4) ++ copyW .ebp H.st.buf .ebx H.N (H.D / 4) ++ H.pad ++ H.atBlk

/-- The MAC to `out`, and our caller's registers back. -/
def finOut : List Instr :=
  (if H.D < H.N then H.atBlk ++ H.out ++ copyW .ebx H.N .edi 0 (H.D / 4) else .mov .eax (.reg .edi) :: H.out) ++
    H.st.restore

def hmacFin : Prog isa :=
  .seq (.block H.st.finPrologue)
  (.seq (H.st.callFin [] Impl.Hmac.Generic.X86.Hash.count1 .ebx H.st.buf)
  (.seq (.block H.finMid)
  (.seq H.cmp
    (.block H.finOut))))

end Hash

end VG.Impl.Pbkdf2.Md.X86
