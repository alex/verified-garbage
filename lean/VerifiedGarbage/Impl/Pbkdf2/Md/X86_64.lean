import VerifiedGarbage.Impl.Hmac.Generic.X86_64
import VerifiedGarbage.Impl.Pbkdf2.X86_64

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function: x86-64 implementation

One implementation of HMAC and PBKDF2-HMAC for every hash function with a
streaming implementation made of the generic Merkle–Damgård code
(`Impl/MdStream/X86_64.lean`): MD5, SHA-1, SHA-256 and the SHA-512 family.
A `Hash` is what the code needs of one of them: its streaming parameters
(`Params`), the size of its digest, the working space its functions get, the
compression function (and its name), its streaming `init`, and the names of
the functions emitted for it.

* HMAC's `init` is the code of `Impl/Hmac/Generic/X86_64.lean` for the
  hash function's streaming `init`, `update` and `finalize` (`Hash.stream`).
  Its `finalize` finalizes the inner state into `scratch`, writes the outer
  hash value and that digest over the inner state (the state that absorbed
  the outer block and the digest), finalizes it, and copies the MAC to
  `out`, all in 32-bit words.
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
open VG.Impl.Hmac.Generic.X86_64 (copy scr byteAt)

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
def stream : Impl.Hmac.Generic.X86_64.Hash :=
  ⟨H.P.B, H.S, H.D, H.P.N, (H.P.so + 48) / 8, H.initN, H.initC, H.updN, H.updC, H.finN, H.finC⟩

/-- `n` 32-bit words from `[src + so]` to `[dst + d]`. -/
def copy32 (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) : List Instr :=
  (List.range n).flatMap (Impl.Pbkdf2.X86_64.cp32 src dst so d)

/-- HMAC's `init`. -/
def hmacInit : Prog isa := H.stream.init

/-! ## HMAC's `finalize`

Registers and buffers as in `Impl/Hmac/Generic/X86_64.lean`'s `finalize`
(`H.stream`): `rbx` = `inner`, `r12` = `outer`, `r13` = `out`, `r15` =
`scratch`, and the digests are written to `scratch + buf`. The outer state
has absorbed one block, so the state that absorbed it and the inner digest
is its hash value followed by a buffer holding the digest: `finMid` writes
it over the inner state, word by word. -/

/-- The outer hash value, then the inner digest after it, over the inner
state. -/
def finMid : List Instr :=
  copy32 .r12 0 .rbx 0 (H.P.N / 4) ++ copy32 .r15 H.stream.buf .rbx H.P.N (H.D / 4)

/-- The MAC to `out`, and our caller's registers back. -/
def finOut : List Instr := copy32 .r15 H.stream.buf .r13 0 (H.D / 4) ++ H.stream.restore

def hmacFin : Prog isa :=
  .seq (.block H.stream.finPrologue)
  (.seq (H.stream.callFin [] [.mov .rsi (.reg .rdx)] H.stream.buf)
  (.seq (.block H.finMid)
  (.seq (H.stream.callFin [.mov .rdi (.reg .rbx)] [.mov32 .rsi (.imm (BitVec.ofNat 32 (H.P.B + H.D)))]
      H.stream.buf)
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

/-- HMAC's functions with our working space: their code saves and restores
our caller's registers where we do, at `sv`. -/
def hh : Impl.Hmac.Generic.X86_64.Hash := { H.stream with W := H.W }

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
