import VerifiedGarbage.Impl.Pbkdf2.X86_64

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function: x86-64 implementation

One implementation of HMAC and PBKDF2-HMAC for every hash function with a
streaming implementation made of the generic Merkle–Damgård code
(`Impl/MdStream/X86_64.lean`): MD5, SHA-1, SHA-256 and the SHA-512 family.
A `Hash` is what the code needs of one of them: its streaming parameters
(`Params`), the size of its digest, the working space its functions get, the
compression function (and its name), its streaming `init`, and the names of
the functions emitted for it. Its streaming functions, as these functions
call them, are a `Stream` (`Hash.stream`).

* HMAC's `init(inner = rdi, outer = rsi, key = rdx, key_len = rcx,
  scratch = r8)` sets each state's hash value with the streaming `init`,
  writes `K₀ ⊕ ipad` into the inner state's buffer (`ipad` a 32-bit word at
  a time, then the key's bytes XORed in) and `K₀ ⊕ opad` into the outer
  one's (from the inner one, a word at a time, XORed with `ipad ⊕ opad`), and
  compresses each buffer into its state's hash value: each state then
  represents its block, as after `update` with it.
* Its `finalize(inner = rdi, outer = rsi, count = rdx, out = rcx,
  scratch = r8)` finalizes the inner state into `scratch`, then computes
  the outer hash, of the outer block and that digest, with one compression,
  as `iterate` does: it writes the outer hash value over the inner state's
  and, into its buffer, the digest followed by the padding of a
  `B + D`-byte message, at fixed offsets in 32-bit words, compresses that
  block, and writes the MAC to `out`.
* `iterate(key = rdi, u = rsi, n = edx, t = rcx, scratch = r8)` is PBKDF2's
  iteration over any Merkle–Damgård hash function (`Impl/Pbkdf2/X86_64.lean`),
  for the hash function's `Params`, digest and compression function: `n`
  steps `U ← HMAC (K₀, U)`, `T ← T ⊕ U`, each two calls of the compression
  function.
* `pbkdf2(password = rdi, password_len = rsi, salt = rdx, salt_len = rcx,
  c = r8d, out = r9, out_len = [rsp + 8], scratch = [rsp + 16])` computes
  the key (hashing a password longer than a block with the streaming
  functions), HMAC's two states with `init`, the inner state after the salt
  once, then each block of the output: `U₁` by `update` with `INT (i)` and
  HMAC's `finalize`, then `iterate`, then as much of `T` as the output
  still needs.

Every function saves our caller's registers in its scratch space, after the
working space of the functions it calls, and keeps its own variables in
`rbx, rbp, r12–r15`, which the functions it calls preserve. Every address
and branch depends only on the pointers, the lengths and the iteration
counts.
-/

namespace VG.Impl.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Impl.MdStream.X86_64 (Params at_ save restore compressAt)

/-! ## The streaming functions, as we call them -/

/-- A streaming hash function's x86-64 functions, as HMAC and PBKDF2 call
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

/-- `[b + r14 + o]`: byte `r14` of the buffer at `b + o`. -/
def byteAt (b : Reg) (o : Nat) : MemOp := { base := b, index := some .r14, scale := 1, disp := o }

/-- `n > 0` bytes copied from `[src + so]` to `[dst + d]`, with `r14` the
index. -/
def copy (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 0)])
    (.loop (.block [.movzx8 .rax (byteAt src so), .store8 (byteAt dst d) .rax,
      .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm (BitVec.ofNat 32 n))]) .ne)

/-- `d ← r15 + o`: an address in `scratch`. -/
def scr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .r15), .alu .add d (.imm (BitVec.ofNat 32 o))]

namespace Stream

variable (H : Stream)

/-- Where our caller's registers are saved in `scratch`: after the working
space of the functions we call. -/
def saved : List (Reg × Nat) :=
  [(.rbx, 8 * H.W), (.rbp, 8 * H.W + 8), (.r12, 8 * H.W + 16), (.r13, 8 * H.W + 24),
    (.r14, 8 * H.W + 32), (.r15, 8 * H.W + 40)]

/-- Where our buffers start in `scratch`. -/
def buf : Nat := 8 * H.W + 48

/-- Saving our caller's registers, with `scratch` in `r8`. -/
def save : List Instr := H.saved.map fun (r, d) => .store (at_ .r8 d) r

/-- Restoring them, with `scratch` in `r15` (restored last). -/
def restore : List Instr := H.saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- A call of `init` on the state at `st` (a register other than `rdi`, or
`rdi` itself). -/
def callInit (st : Reg) : Prog isa :=
  .seq (.block [.mov .rdi (.reg st)]) (.call H.initN H.initC)

/-- A call of `finalize` on the state at `rdi` (set by `st`), with the count
`count` (set by `count`) and the digest to `scratch + o`. -/
def callFin (st count : List Instr) (o : Nat) : Prog isa :=
  .seq (.block (st ++ count ++ scr .rdx o ++ [.mov .rcx (.reg .r15)])) (.call H.finN H.finC)

/-- Saving our caller's registers and setting up ours for HMAC's `finalize`:
`rbx` = `inner`, `r12` = `outer`, `r13` = `out`, `r15` = `scratch`. -/
def finPrologue : List Instr :=
  H.save ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rcx),
    .mov .r15 (.reg .r8)]

end Stream

/-- A Merkle–Damgård hash function's x86-64 functions, as HMAC and PBKDF2
call them. -/
structure Hash where
  /-- The streaming parameters: the sizes, the length field and the digest. -/
  P : Params
  /-- The size of the digest (at most `N`: the SHA-512 family's truncated
  members output part of the hash value). -/
  D : Nat
  /-- The words of working space our functions get (`VG.Spec.Hmac.Instance.scratch`). -/
  W : Nat
  /-- The compression function, and its name. -/
  compN : String
  compC : Prog isa
  /-- The streaming `init`, and its name. -/
  initN : String
  initC : Prog isa
  /-- The names of the streaming `update` and `finalize` made with the
  compression function. -/
  updN : String
  finN : String
  /-- The names of HMAC's `init` and `finalize` and of PBKDF2's `iterate`. -/
  hmacInitN : String
  hmacFinN : String
  iterN : String

namespace Hash

variable (H : Hash)

/-- The size of the streaming state. -/
abbrev S : Nat := H.P.N + H.P.B

/-- The streaming `update` and `finalize`. -/
def updC : Prog isa := MdStream.X86_64.update H.P H.compN H.compC
def finC : Prog isa := MdStream.X86_64.finalize H.P H.compN H.compC

/-- The streaming functions, as HMAC calls them: `update` and `finalize`
use `so + 48` bytes of working space, and `finalize` writes the `N`-byte
digest of the hash value. -/
def stream : Stream :=
  ⟨H.P.B, H.S, H.D, H.P.N, (H.P.so + 48) / 8, H.initN, H.initC, H.updN, H.updC, H.finN, H.finC⟩

/-- `n` 32-bit words from `[src + so]` to `[dst + d]`. -/
def copy32 (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) : List Instr :=
  (List.range n).flatMap (Impl.Pbkdf2.X86_64.cp32 src dst so d)

/-! ## HMAC's `init`

Registers: `rbx` = `inner`, `r12` = `outer`, `r15` = `scratch`, `rbp` =
`key`, `r13` = `key_len`, `r14` = the byte index. Each state's buffer
receives its padded key, `K₀ ⊕ ipad` at `rbx + N` and `K₀ ⊕ opad` at
`r12 + N`, after `init` has set its hash value; then one compression each
makes the state represent that block. -/

/-- Saving our caller's registers, and setting up ours. -/
def initPrologue : List Instr :=
  H.stream.save ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .r8),
    .mov .rbp (.reg .rdx), .mov .r13 (.reg .rcx)]

/-- `ipad` into every byte of the inner buffer, a word at a time; then the
byte index for the key, and whether there is a key byte at all. -/
def ipadFill : List Instr :=
  .mov32 .rax (.imm 0x36363636) ::
    (List.range (H.P.B / 4)).map (fun k => .store32 (at_ .rbx (H.P.N + 4 * k)) .rax) ++
    [.mov32 .r14 (.imm 0), .alu .test .r13 (.reg .r13)]

/-- The key bytes, XORed with `ipad`, over the first `key_len` bytes of the
inner buffer. -/
def keyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (byteAt .rbp 0), .alu32 .xor .rax (.imm 0x36),
    .store8 (byteAt .rbx H.P.N) .rax, .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .r13)]) .ne

/-- Word `k` of the outer buffer: word `k` of the inner one, `K₀ ⊕ ipad`,
XORed with `ipad ⊕ opad`. -/
def opadW (k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rbx (H.P.N + 4 * k))), .alu32 .xor .rax (.imm 0x6a6a6a6a),
    .store32 (at_ .r12 (H.P.N + 4 * k)) .rax]

/-- The outer buffer, and the inner block's address for the compression
function. -/
def opadFill : List Instr :=
  (List.range (H.P.B / 4)).flatMap H.opadW ++
    [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 H.P.N))]

/-- Both padded keys into the buffers: the part of `init` between its calls. -/
def initKeys : Prog isa :=
  .seq (.block H.ipadFill) (.seq (.ite .e (.block []) H.keyLoop) (.block H.opadFill))

/-- The outer state's hash value and block, for the compression function. -/
def initOuter : List Instr :=
  [.mov .rbx (.reg .r12), .mov .rsi (.reg .r12), .alu .add .rsi (.imm (BitVec.ofNat 32 H.P.N))]

def hmacInit : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (H.stream.callInit .rbx)
  (.seq (H.stream.callInit .r12)
  (.seq H.initKeys
  (.seq (compressAt H.compN H.compC)
  (.seq (.block H.initOuter)
  (.seq (compressAt H.compN H.compC)
    (.block H.stream.restore)))))))

/-! ## HMAC's `finalize`

Up to the inner digest, which the streaming `finalize` writes to
`scratch + buf`, the registers are those of `Stream.finPrologue`: `rbx` =
`inner`, `r12` = `outer`, `r13` = `out`, `r15` = `scratch`. The outer state has absorbed one block, so the outer hash, of
that block and the `D`-byte digest, is one compression of the outer hash
value with the block of the digest and the padding of a `B + D`-byte
message, as in `iterate` (`Impl/Pbkdf2/X86_64.lean`). The inner state is no
longer needed, so it holds them: its hash value at `rbx` and the block in
its buffer, at `rbp = rbx + N`. -/

/-- The outer hash value over the inner state's, the inner digest into its
buffer, then the padding after it (`padLen`), and the block's address for
the compression function. -/
def finMid : List Instr :=
  copy32 .r12 0 .rbx 0 (H.P.N / 4) ++ copy32 .r15 H.stream.buf .rbx H.P.N (H.D / 4) ++
    [.mov .rbp (.reg .rbx), .alu .add .rbp (.imm (BitVec.ofNat 32 H.P.N))] ++
    Impl.Pbkdf2.X86_64.padLen H.P H.D ++ [.mov .rsi (.reg .rbp)]

/-- The MAC to `out`: the digest of the hash value, written there directly,
or for a digest shorter than the hash value (`P.out` writes `N` bytes) into
the block and its first `D` bytes copied; and our caller's registers back. -/
def finOut : List Instr :=
  (if H.D < H.P.N then H.P.out ++ copy32 .rbp 0 .r13 0 (H.D / 4) else .mov .rbp (.reg .r13) :: H.P.out) ++
    H.stream.restore

def hmacFin : Prog isa :=
  .seq (.block H.stream.finPrologue)
  (.seq (H.stream.callFin [] [.mov .rsi (.reg .rdx)] H.stream.buf)
  (.seq (.block H.finMid)
  (.seq (compressAt H.compN H.compC)
    (.block H.finOut))))

/-! ## `iterate`

PBKDF2's iteration over any Merkle–Damgård hash function
(`Impl/Pbkdf2/X86_64.lean`), calling the compression function directly. -/

def iterate : Prog isa := Impl.Pbkdf2.X86_64.iterate H.P H.D H.compN H.compC

/-! ## `pbkdf2`

`scratch` starts with the working space of the functions we call (`8 W`
bytes); then come our caller's registers, `out` and `c - 1`, the HMAC key's
inner and outer streaming states, the inner state after the salt, a
working state, `U`, `T`, the hashed password and `INT (i)`. Registers, until
the salt is absorbed: `rbx` = `password`, `rbp` = `password_len`, `r12` =
`salt`, `r13` = `salt_len`; then `rbx` = `i`, `rbp` = `salt_len`, `r12` = the
bytes of output left, `r13` = where they go. `r15` = `scratch`, and `r14` is
the byte index. -/

/-- Where our caller's registers are saved. -/
def sv : Nat := 8 * H.W

/-- Where `out` and `c - 1` are kept. -/
def outO : Nat := H.sv + 48
def cO : Nat := H.sv + 56

/-- The HMAC key's states, the salted inner state and the working state. -/
def st0O : Nat := H.sv + 64
def st1O : Nat := H.st0O + H.S
def stSO : Nat := H.st1O + H.S
def stWO : Nat := H.stSO + H.S

/-- `U`, `T`, the hashed password and `INT (i)`. -/
def uO : Nat := H.stWO + H.S
def tO : Nat := H.uO + H.D
def hkO : Nat := H.tO + H.D
def intO : Nat := H.hkO + H.P.N

/-- The streaming functions with our working space: our code saves and
restores our caller's registers where HMAC's does, at `sv`. -/
def hh : Stream := { H.stream with W := H.W }

/-- Load `scratch` from the stack, keeping `c` in `r10`. -/
def loadScr : List Instr := [.mov .r10 (.reg .r8), .mov .r8 (.mem (at_ .rsp 16))]

/-- Save our caller's registers, keep `out` and `c - 1`, and set up ours;
then compare the password's length with the block size. -/
def entry : List Instr :=
  H.hh.save ++
    [.mov .r15 (.reg .r8), .store (at_ .r15 H.outO) .r9, .mov32 .rax (.reg .r10),
      .alu .sub .rax (.imm 1), .store (at_ .r15 H.cO) .rax,
      .mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rcx),
      .alu .cmp .rbp (.imm (BitVec.ofNat 32 (H.P.B + 1)))]

/-- A password longer than a block: its digest, into `scratch`, is the key. -/
def hashKey : Prog isa :=
  .seq (.block (scr .rdi H.stWO))
  (.seq (.call H.initN H.initC)
  (.seq (.block (scr .rdi H.stWO ++ [.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbx), .mov .rcx (.reg .rbp),
      .mov .r8 (.reg .r15)]))
  (.seq (.call H.updN H.updC)
  (.seq (.block (scr .rdi H.stWO ++ [.mov .rsi (.reg .rbp)] ++ scr .rdx H.hkO ++ [.mov .rcx (.reg .r15)]))
  (.seq (.call H.finN H.finC)
    (.block (scr .rdx H.hkO ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))])))))))

/-- The key (at `rdx`, `rcx` bytes). -/
def key : Prog isa :=
  .ite .ae H.hashKey (.block [.mov .rdx (.reg .rbx), .mov .rcx (.reg .rbp)])

/-- HMAC's states for the key, then the inner one after the salt. -/
def setup : Prog isa :=
  .seq (.block (scr .rdi H.st0O ++ scr .rsi H.st1O ++ [.mov .r8 (.reg .r15)]))
  (.seq (.call H.hmacInitN H.hmacInit)
  (.seq (copy .r15 H.st0O .r15 H.stSO H.S)
  (.seq (.block (scr .rdi H.stSO ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 H.P.B)), .mov .rdx (.reg .r12),
      .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)]))
    (.call H.updN H.updC))))

/-- The registers of the loop over the blocks of the output. -/
def loopRegs : List Instr :=
  [.mov .rbp (.reg .r13), .mov .r13 (.mem (at_ .r15 H.outO)), .mov .r12 (.mem (at_ .rsp 8)),
    .mov32 .rbx (.imm 1), .alu .test .r12 (.reg .r12)]

/-- The loop copying `rcx` bytes of `T` to `r13`. -/
def outLoop : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 0)])
    (.loop (.block [.movzx8 .rax (byteAt .r15 H.tO), .store8 { base := .r13, index := some .r14 } .rax,
      .alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .rcx)]) .ne)

/-- `INT (i)`, and `update`'s arguments: the working state and `INT (i)`. -/
def intArgs : List Instr :=
  [.mov32 .rax (.reg .rbx), .bswap32 .rax, .store32 (at_ .r15 H.intO) .rax] ++
    scr .rdi H.stWO ++ [.mov .rsi (.reg .rbp), .alu .add .rsi (.imm (BitVec.ofNat 32 H.P.B))] ++
    scr .rdx H.intO ++ [.mov32 .rcx (.imm 4), .mov .r8 (.reg .r15)]

/-- HMAC's `finalize`'s arguments: the working state, the outer state, the
bytes absorbed and `U`. -/
def finArgs : List Instr :=
  scr .rdi H.stWO ++ scr .rsi H.st1O ++
    [.mov .rdx (.reg .rbp), .alu .add .rdx (.imm (BitVec.ofNat 32 (H.P.B + 4)))] ++ scr .rcx H.uO ++
    [.mov .r8 (.reg .r15)]

/-- `iterate`'s arguments: the key's states, `U`, `c - 1` and `T`. -/
def iterArgs : List Instr :=
  scr .rdi H.st0O ++ scr .rsi H.uO ++ [.mov .rdx (.mem (at_ .r15 H.cO))] ++ scr .rcx H.tO ++
    [.mov .r8 (.reg .r15)]

/-- The bytes of `T` the output still needs: `min (r12, D)`. -/
def outLen : Prog isa :=
  .seq (.block [.mov32 .rcx (.imm (BitVec.ofNat 32 H.D)), .alu .cmp .r12 (.reg .rcx)])
    (.ite .b (.block [.mov .rcx (.reg .r12)]) (.block []))

/-- The next block's number, where its bytes go, and how many are left. -/
def advance : List Instr := [.alu .add .r13 (.reg .rcx), .alu .add .rbx (.imm 1), .alu .sub .r12 (.reg .rcx)]

/-- One block of the output. -/
def block : Prog isa :=
  .seq (copy .r15 H.stSO .r15 H.stWO H.S)
  (.seq (.block H.intArgs)
  (.seq (.call H.updN H.updC)
  (.seq (.block H.finArgs)
  (.seq (.call H.hmacFinN H.hmacFin)
  (.seq (copy .r15 H.uO .r15 H.tO H.D)
  (.seq (.block H.iterArgs)
  (.seq (.call H.iterN H.iterate)
  (.seq H.outLen
  (.seq H.outLoop
    (.block advance))))))))))

/-- Restoring our caller's registers. -/
def exit : List Instr := H.hh.restore

def pbkdf2 : Prog isa :=
  .seq (.block loadScr)
  (.seq (.block H.entry)
  (.seq H.key
  (.seq H.setup
  (.seq (.block H.loopRegs)
  (.seq (.ite .e (.block []) (.loop H.block .ne))
    (.block H.exit))))))

end Hash

end VG.Impl.Pbkdf2.Md.X86_64
