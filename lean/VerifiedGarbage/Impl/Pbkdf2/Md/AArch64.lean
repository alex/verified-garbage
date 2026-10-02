import VerifiedGarbage.Impl.Pbkdf2.AArch64

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function: AArch64 implementation

The same design as on x86-64 (`Impl/Pbkdf2/Md/X86_64.lean`): one
implementation of HMAC and PBKDF2-HMAC for every Merkle–Damgård hash
function (MD5, SHA-1, SHA-256 and the SHA-512 family). A `Hash` is what the
code needs of one of them: what PBKDF2's iteration needs of its code
(`Params`), the size of its digest, the working space its functions get, the
compression function, its streaming `init`, `update` and `finalize` (and
their names), and the names of the functions emitted for it. Its streaming
functions, as these functions call them, are a `Stream` (`Hash.stream`).

* HMAC's `init(inner = x0, outer = x1, key = x2, key_len = x3, scratch = x4)`
  sets each state's hash value with the streaming `init`, writes
  `K₀ ⊕ ipad` into the inner state's buffer (`ipad` a 32-bit word at a time,
  then the key's bytes XORed in) and `K₀ ⊕ opad` into the outer one's (from
  the inner one, a word at a time, XORed with `ipad ⊕ opad`), and compresses
  each buffer into its state's hash value: each state then represents its
  block, as after `update` with it.
* Its `finalize(inner = x0, outer = x1, count = x2, out = x3, scratch = x4)`
  finalizes the inner state into `scratch`, then computes the outer hash, of
  the outer block and that digest, with one compression, as `iterate` does:
  it writes the outer hash value over the inner state's and, into its
  buffer, the digest followed by the padding of a `B + D`-byte message, at
  fixed offsets in 32-bit words, compresses that block, and writes the MAC
  to `out`.
* `iterate(key = x0, u = x1, n = w2, t = x3, scratch = x4)` is PBKDF2's
  iteration over any Merkle–Damgård hash function
  (`Impl/Pbkdf2/AArch64.lean`), for the hash function's `Params`, digest and
  compression function: `n` steps `U ← HMAC (K₀, U)`, `T ← T ⊕ U`, each two
  calls of the compression function.
* `pbkdf2(password = x0, password_len = x1, salt = x2, salt_len = x3,
  c = w4, out = x5, out_len = x6, scratch = x7)` computes the key (hashing
  a password longer than a block with the streaming functions), HMAC's two
  states with `init`, the inner state after the salt once, then each block
  of the output: `U₁` by `update` with `INT (i)` and HMAC's `finalize`, then
  `iterate`, then as much of `T` as the output still needs.

Every function saves our caller's registers and its return address `x30`
(which each call replaces) in its scratch space, after the working space of
the functions it calls, so it uses no stack of its own and has no frames,
and keeps its own variables in `x19`–`x24`, which the functions it calls
preserve. Every address and branch depends only on the pointers, the lengths
and the iteration counts.
-/

namespace VG.Impl.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.MdStream.AArch64 (mov compressAt)
open VG.Impl.Pbkdf2.AArch64 (Params cp32)

/-! ## The streaming functions, as we call them -/

/-- A streaming hash function's AArch64 functions, as HMAC and PBKDF2 call
them: the block size `B`, the sizes of the streaming state (`S`), of the
digest (`D`) and of what `finalize` writes (`F`, at least `D`), the words of
working space of `update` and `finalize` (`W`), and the three functions,
with their names. -/
structure Stream where
  B : Nat
  S : Nat
  D : Nat
  F : Nat
  W : Nat
  initN : String
  initC : Prog isa
  updN : String
  updC : Prog isa
  finN : String
  finC : Prog isa

namespace Stream

variable (H : Stream)

/-- Where our caller's registers and our return address are saved in
`scratch`: after the working space of the functions we call (`x23`, which
holds `scratch`, last). -/
def saved : List (Reg × Nat) :=
  [(.x19, 8 * H.W), (.x20, 8 * H.W + 8), (.x21, 8 * H.W + 16), (.x22, 8 * H.W + 24),
    (.x24, 8 * H.W + 32), (.x30, 8 * H.W + 40), (.x23, 8 * H.W + 48)]

/-- Where our buffers start in `scratch`. -/
def buf : Nat := 8 * H.W + 56

/-- Saving them, with `scratch` in `x4`. -/
def save : List Instr := H.saved.map fun (r, d) => .str .x r .x4 d

/-- Restoring them, with `scratch` in `x23` (restored last). -/
def restore : List Instr := H.saved.map fun (r, d) => .ldr .x r .x23 d

/-- A call of `init` on the state at `st`. -/
def callInit (st : Reg) : Prog isa :=
  .seq (.block [mov .x0 st]) (.call H.initN H.initC)

/-- A call of `finalize` on the state at `x0` (set by `st`), with the count
`count` (set by `count`) and the digest to `scratch + o`. -/
def callFin (st count : List Instr) (o : Nat) : Prog isa :=
  .seq (.block (st ++ count ++ [.addImm .x .x2 .x23 o, mov .x3 .x23])) (.call H.finN H.finC)

/-- Saving our caller's registers and setting up ours for HMAC's `finalize`:
`x19` = `inner`, `x20` = `outer`, `x21` = `out`, `x23` = `scratch`. -/
def finPrologue : List Instr :=
  H.save ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x3, mov .x23 .x4]

end Stream

/-- A Merkle–Damgård hash function's AArch64 functions, as HMAC and PBKDF2
call them. -/
structure Hash where
  /-- What PBKDF2's iteration needs of its code: the sizes, the scratch space
  of the compression function, the length field and the digest. -/
  P : Params
  /-- The size of the digest (at most `N`: the SHA-512 family's truncated
  members output part of the hash value). -/
  D : Nat
  /-- The words of working space our functions get (`VG.Spec.Hmac.Instance.scratch`). -/
  W : Nat
  /-- The compression function, and its name. -/
  compN : String
  compC : Prog isa
  /-- The streaming `init`, `update` and `finalize`, and their names:
  `update` and `finalize` use `so + 48` bytes of working space. -/
  initN : String
  initC : Prog isa
  updN : String
  updC : Prog isa
  finN : String
  finC : Prog isa
  /-- The names of HMAC's `init` and `finalize` and of PBKDF2's `iterate`. -/
  hmacInitN : String
  hmacFinN : String
  iterN : String

namespace Hash

variable (H : Hash)

/-- The size of the streaming state. -/
abbrev S : Nat := H.P.N + H.P.B

/-- The streaming functions, as HMAC calls them: `update` and `finalize`
use `so + 48` bytes of working space, and `finalize` writes the `N`-byte
digest of the hash value. -/
def stream : Stream :=
  ⟨H.P.B, H.S, H.D, H.P.N, (H.P.so + 48) / 8, H.initN, H.initC, H.updN, H.updC, H.finN, H.finC⟩

/-- `n` 32-bit words from `[src + so]` to `[dst + d]`. -/
def copy32 (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) : List Instr :=
  (List.range n).flatMap (cp32 src dst so d)

/-! ## HMAC's `init`

Registers: `x19` = `inner`, `x20` and `x23` = `scratch` (for the compression
function and for `restore`), `x21` = `outer`, `x22` = `key`, `x24` =
`key_len`; in the key loop, `x10` = the byte index and `x11` the bytes left.
Each state's buffer receives its padded key, `K₀ ⊕ ipad` at `x19 + N` and
`K₀ ⊕ opad` at `x21 + N`, after `init` has set its hash value; then one
compression each makes the state represent that block. -/

/-- Saving our caller's registers and our return address, and setting up
ours. -/
def initPrologue : List Instr :=
  H.stream.save ++ [mov .x19 .x0, mov .x20 .x4, mov .x21 .x1, mov .x22 .x2, mov .x23 .x4, mov .x24 .x3]

/-- `ipad` into every byte of the inner buffer, a word at a time (`x14` =
`ipad` in every byte of its low word); then the byte index for the key. -/
def ipadFill : List Instr :=
  [.movz .w .x14 0x3636 0, .movk .w .x14 0x3636 1] ++
    (List.range (H.P.B / 4)).map (fun k => .str .w .x14 .x19 (H.P.N + 4 * k)) ++ [.movz .x .x10 0 0]

/-- The key bytes, XORed with `ipad`, over the first `key_len` bytes of the
inner buffer. -/
def keyLoop : Prog isa :=
  .loop (.block [.add .x .x13 .x22 .x10, .ldrb .x9 .x13 0, .logic .eor .x .x9 .x9 .x14,
    .add .x .x12 .x19 .x10, .strb .x9 .x12 H.P.N, .addImm .x .x10 .x10 1, .sub .x .x11 .x24 .x10])
    (.nonzero .x .x11)

/-- Word `k` of the outer buffer: word `k` of the inner one, `K₀ ⊕ ipad`,
XORed with `ipad ⊕ opad` (`x15`). -/
def opadW (k : Nat) : List Instr :=
  [.ldr .w .x9 .x19 (H.P.N + 4 * k), .logic .eor .x .x9 .x9 .x15, .str .w .x9 .x21 (H.P.N + 4 * k)]

/-- The outer buffer, and the inner block's address for the compression
function. -/
def opadFill : List Instr :=
  [.movz .w .x15 0x6a6a 0, .movk .w .x15 0x6a6a 1] ++ (List.range (H.P.B / 4)).flatMap H.opadW ++
    [.addImm .x .x1 .x19 H.P.N]

/-- Both padded keys into the buffers: the part of `init` between its calls. -/
def initKeys : Prog isa :=
  .seq (.block H.ipadFill) (.seq (.ite (.zero .x .x24) (.block []) H.keyLoop) (.block H.opadFill))

/-- The outer state's hash value and block, for the compression function. -/
def initOuter : List Instr := [mov .x19 .x21, .addImm .x .x1 .x21 H.P.N]

def hmacInit : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (H.stream.callInit .x19)
  (.seq (H.stream.callInit .x21)
  (.seq H.initKeys
  (.seq (compressAt H.compN H.compC)
  (.seq (.block H.initOuter)
  (.seq (compressAt H.compN H.compC)
    (.block H.stream.restore)))))))

/-! ## HMAC's `finalize`

Up to the inner digest, which the streaming `finalize` writes to
`scratch + buf`, the registers are those of `Stream.finPrologue`: `x19` =
`inner`, `x20` = `outer`, `x21` = `out`, `x23` = `scratch`. The outer state has absorbed one block, so the outer hash, of
that block and the `D`-byte digest, is one compression of the outer hash
value with the block of the digest and the padding of a `B + D`-byte
message, as in `iterate` (`Impl/Pbkdf2/AArch64.lean`). The inner state is no
longer needed, so it holds them: its hash value at `x19` and the block in
its buffer, at `x21 = x19 + N`. For the compression function and the
digest, `x20` becomes `scratch` and `x24` keeps `out`. -/

/-- The outer hash value over the inner state's, the inner digest into its
buffer, then the padding after it (`padLen`), and the block's address for
the compression function. -/
def finMid : List Instr :=
  copy32 .x20 0 .x19 0 (H.P.N / 4) ++ copy32 .x23 H.stream.buf .x19 H.P.N (H.D / 4) ++
    [mov .x24 .x21, .addImm .x .x21 .x19 H.P.N, mov .x20 .x23] ++ Impl.Pbkdf2.AArch64.padLen H.P H.D ++
    [mov .x1 .x21]

/-- The MAC to `out`: the digest of the hash value, written there directly,
or for a digest shorter than the hash value (`P.out` writes `N` bytes) into
the block and its first `D` bytes copied; and our caller's registers back. -/
def finOut : List Instr :=
  (if H.D < H.P.N then H.P.out ++ copy32 .x21 0 .x24 0 (H.D / 4) else mov .x21 .x24 :: H.P.out) ++
    H.stream.restore

def hmacFin : Prog isa :=
  .seq (.block H.stream.finPrologue)
  (.seq (H.stream.callFin [] [mov .x1 .x2] H.stream.buf)
  (.seq (.block H.finMid)
  (.seq (compressAt H.compN H.compC)
    (.block H.finOut))))

/-! ## `iterate`

PBKDF2's iteration over any Merkle–Damgård hash function
(`Impl/Pbkdf2/AArch64.lean`), calling the compression function directly. -/

def iterate : Prog isa := Impl.Pbkdf2.AArch64.iterate H.P H.D H.compN H.compC

/-! ## `pbkdf2`

`scratch` starts with the working space of the functions we call (`8 W`
bytes); then come our caller's registers and our return address (where
HMAC's functions keep theirs, `hh`), `out`, `c - 1` and `out_len`, the HMAC
key's inner and outer streaming states, the inner state after the salt, a
working state, `U`, `T`, the hashed password and `INT (i)`. Registers, until
the salt is absorbed: `x19` = `password`, `x20` = `password_len`, `x21` =
`salt`, `x22` = `salt_len`; then `x19` = `i`, `x20` = `salt_len`, `x21` =
the bytes of output left, `x22` = where they go. `x23` = `scratch`, and
`x24` is the byte index. -/

/-- Where our caller's registers are saved. -/
def sv : Nat := 8 * H.W

/-- Where `out`, `c - 1` and `out_len` are kept. -/
def outO : Nat := H.sv + 56
def cO : Nat := H.sv + 64
def olO : Nat := H.sv + 72

/-- The HMAC key's states, the salted inner state and the working state. -/
def st0O : Nat := H.sv + 80
def st1O : Nat := H.st0O + H.S
def stSO : Nat := H.st1O + H.S
def stWO : Nat := H.stSO + H.S

/-- `U`, `T`, the hashed password and `INT (i)`. -/
def uO : Nat := H.stWO + H.S
def tO : Nat := H.uO + H.D
def hkO : Nat := H.tO + H.D
def intO : Nat := H.hkO + H.P.N

/-- HMAC's functions with our working space: their code saves and restores
our caller's registers where we do, at `sv`. -/
def hh : Stream := { H.stream with W := H.W }

/-- Keep `c` in `x10`, and `scratch` in `x4`, where `hh.save` wants it. -/
def entryPre : List Instr := [mov .x10 .x4, mov .x4 .x7]

/-- Keep `out`, `c - 1` and `out_len`, and set up our registers. -/
def entryPost : List Instr :=
  [mov .x23 .x4, .str .x .x5 .x23 H.outO, .subImm .w .x9 .x10 1, .str .x .x9 .x23 H.cO,
    .str .x .x6 .x23 H.olO, mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3]

/-- Save our caller's registers, keep `out`, `c - 1` and `out_len`, and set
up ours. -/
def entry : List Instr := entryPre ++ H.hh.save ++ H.entryPost

/-- `init`'s argument: the working state. -/
def hkInit : List Instr := [.addImm .x .x0 .x23 H.stWO]

/-- `update`'s arguments: the working state and the password. -/
def hkUpd : List Instr := [.addImm .x .x0 .x23 H.stWO, .movz .x .x1 0 0, mov .x2 .x19, mov .x3 .x20, mov .x4 .x23]

/-- `finalize`'s arguments: the working state, and the digest into `scratch`. -/
def hkFin : List Instr := [.addImm .x .x0 .x23 H.stWO, mov .x1 .x20, .addImm .x .x2 .x23 H.hkO, mov .x3 .x23]

/-- The digest as the key. -/
def hkKey : List Instr := [.addImm .x .x2 .x23 H.hkO, .movz .x .x3 (BitVec.ofNat 16 H.D) 0]

/-- A password longer than a block: its digest, into `scratch`, is the key. -/
def hashKey : Prog isa :=
  .seq (.block H.hkInit)
  (.seq (.call H.initN H.initC)
  (.seq (.block H.hkUpd)
  (.seq (.call H.updN H.updC)
  (.seq (.block H.hkFin)
  (.seq (.call H.finN H.finC)
    (.block H.hkKey))))))

/-- The password as the key. -/
def short : List Instr := [mov .x2 .x19, mov .x3 .x20]

/-- `password_len >> log₂ B`, zero if the password is shorter than a block. -/
def keyShr : List Instr := [.lsr .x .x9 .x20 (Nat.log2 H.P.B)]

/-- `password_len - B`, zero if the password is a block. -/
def keySub : List Instr := [.subImm .x .x9 .x20 H.P.B]

/-- The key (at `x2`, `x3` bytes): the password if it is at most a block
(`password_len >> log₂ B = 0`, or `password_len = B`), otherwise its
digest. -/
def key : Prog isa :=
  .seq (.block H.keyShr)
    (.ite (.zero .x .x9) (.block short)
      (.seq (.block H.keySub) (.ite (.zero .x .x9) (.block short) H.hashKey)))

/-- HMAC's `init`'s arguments: its two states, the key (already in `x2` and
`x3`) and `scratch`. -/
def initArgs : List Instr := [.addImm .x .x0 .x23 H.st0O, .addImm .x .x1 .x23 H.st1O, mov .x4 .x23]

/-- The inner state copied, and `update`'s arguments: the copy and the salt. -/
def saltArgs : List Instr :=
  copy32 .x23 H.st0O .x23 H.stSO (H.S / 4) ++
    [.addImm .x .x0 .x23 H.stSO, .movz .x .x1 (BitVec.ofNat 16 H.P.B) 0, mov .x2 .x21, mov .x3 .x22,
      mov .x4 .x23]

/-- HMAC's states for the key, then the inner one after the salt. -/
def setup : Prog isa :=
  .seq (.block H.initArgs)
  (.seq (.call H.hmacInitN H.hmacInit)
  (.seq (.block H.saltArgs)
    (.call H.updN H.updC)))

/-- The registers of the loop over the blocks of the output. -/
def loopRegs : List Instr :=
  [mov .x20 .x22, .ldr .x .x22 .x23 H.outO, .ldr .x .x21 .x23 H.olO, .movz .x .x19 1 0]

/-- The loop copying `x11` bytes of `T` to `x22`: `x24` counts the bytes
copied, `x11` those left. -/
def outLoop : Prog isa :=
  .seq (.block [.movz .x .x24 0 0])
    (.loop (.block [.add .x .x12 .x23 .x24, .ldrb .x9 .x12 H.tO, .add .x .x13 .x22 .x24, .strb .x9 .x13 0,
      .addImm .x .x24 .x24 1, .subImm .x .x11 .x11 1]) (.nonzero .x .x11))

/-- The salted inner state copied to the working state, `INT (i)`, and `update`'s
arguments: the working state and `INT (i)`. -/
def intArgs : List Instr :=
  copy32 .x23 H.stSO .x23 H.stWO (H.S / 4) ++
    [.rev32 .x9 .x19, .str .w .x9 .x23 H.intO, .addImm .x .x0 .x23 H.stWO, .addImm .x .x1 .x20 H.P.B,
      .addImm .x .x2 .x23 H.intO, .movz .x .x3 4 0, mov .x4 .x23]

/-- HMAC's `finalize`'s arguments: the working state, the outer state, the
bytes absorbed and `U`. -/
def finArgs : List Instr :=
  [.addImm .x .x0 .x23 H.stWO, .addImm .x .x1 .x23 H.st1O, .addImm .x .x2 .x20 (H.P.B + 4),
    .addImm .x .x3 .x23 H.uO, mov .x4 .x23]

/-- `U` copied to `T`, and `iterate`'s arguments: the key's states, `U`, `c - 1` and
`T`. -/
def iterArgs : List Instr :=
  copy32 .x23 H.uO .x23 H.tO (H.D / 4) ++
    [.addImm .x .x0 .x23 H.st0O, .addImm .x .x1 .x23 H.uO, .ldr .x .x2 .x23 H.cO, .addImm .x .x3 .x23 H.tO,
      mov .x4 .x23]

/-- The bytes of `T` the output still needs: `min (x21, D)`, from the sign of
`x21 - D` (`x21` is below 2⁶³). -/
def outLen : Prog isa :=
  .seq (.block [.movz .x .x11 (BitVec.ofNat 16 H.D) 0, .subImm .x .x9 .x21 H.D, .lsr .x .x9 .x9 63])
    (.ite (.zero .x .x9) (.block []) (.block [mov .x11 .x21]))

/-- The next block's number, where its bytes go, and how many are left
(`x24` bytes were copied). -/
def advance : List Instr := [.add .x .x22 .x22 .x24, .addImm .x .x19 .x19 1, .sub .x .x21 .x21 .x24]

/-- One block of the output. -/
def block : Prog isa :=
  .seq (.block H.intArgs)
  (.seq (.call H.updN H.updC)
  (.seq (.block H.finArgs)
  (.seq (.call H.hmacFinN H.hmacFin)
  (.seq (.block H.iterArgs)
  (.seq (.call H.iterN H.iterate)
  (.seq H.outLen
  (.seq H.outLoop
    (.block advance))))))))

/-- Restoring our caller's registers and our return address. -/
def exit : List Instr := H.hh.restore

def pbkdf2 : Prog isa :=
  .seq (.block H.entry)
  (.seq H.key
  (.seq H.setup
  (.seq (.block H.loopRegs)
  (.seq (.ite (.zero .x .x21) (.block []) (.loop H.block (.nonzero .x .x21)))
    (.block H.exit)))))

end Hash

end VG.Impl.Pbkdf2.Md.AArch64
