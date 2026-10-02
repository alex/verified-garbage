import VerifiedGarbage.Impl.Sha256.X86_64
import VerifiedGarbage.Impl.Sha1.X86_64.Stream
import VerifiedGarbage.Impl.Md5.X86_64.Stream
import VerifiedGarbage.Impl.Sha512.X86_64.Stream

/-!
# HMAC over any streaming hash function: x86-64 implementation

One implementation of `vg_hmac_<hash>_init` and `vg_hmac_<hash>_finalize`
(see `VG.Spec.Hmac.Instance`) for every hash function `H` with a streaming
implementation, made only of calls of `H`'s own `init`, `update` and
`finalize` (`Hash`), and of byte loops around them.

* `init(inner = rdi, outer = rsi, key = rdx, key_len = rcx, scratch = r8)`
  writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` into `scratch`, then starts each state
  with `init` and absorbs its padded key with `update`, for a key of at most
  a block; `initAny`, for a key of any length, first replaces a longer key
  by its digest (`hashKey`).
* `finalize(inner = rdi, outer = rsi, count = rdx, out = rcx, scratch = r8)`
  finalizes the inner state into `scratch`, copies the outer state over the
  inner one, absorbs that digest into it with `update`, finalizes it into
  `scratch` again, and copies the MAC to `out`.

`scratch` starts with the working space of the functions we call (`8 W`
bytes); then come our caller's registers (`saved`), then our buffers. The
functions we call preserve `rbx, rbp, r12–r15`, so our variables live
there; `r15` is always `scratch`.
-/

namespace VG.Impl.Hmac.Generic.X86_64

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_)

/-- A streaming hash function's x86-64 functions, as we call them: the block
size `B`, the sizes of the streaming state (`S`), of the digest (`D`) and of
what `finalize` writes (`F`, at least `D`), the words of working space of
`update` and `finalize` (`W`), and the three functions, with their names. -/
structure Hash where
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

namespace Hash

variable (H : Hash)

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

/-- A call of `init` on the state at `scratch + o`. -/
def callInit' (o : Nat) : Prog isa :=
  .seq (.block (scr .rdi o)) (.call H.initN H.initC)

/-- A call of `update` on the state at `rdi` (set by `st`), with the count
`count` and the `len` bytes at `scratch + o`. -/
def callUpd (st : List Instr) (count o len : Nat) : Prog isa :=
  .seq (.block (st ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 count))] ++ scr .rdx o ++
      [.mov32 .rcx (.imm (BitVec.ofNat 32 len)), .mov .r8 (.reg .r15)]))
    (.call H.updN H.updC)

/-- A call of `finalize` on the state at `rdi` (set by `st`), with the count
`count` (set by `count`) and the digest to `scratch + o`. -/
def callFin (st count : List Instr) (o : Nat) : Prog isa :=
  .seq (.block (st ++ count ++ scr .rdx o ++ [.mov .rcx (.reg .r15)])) (.call H.finN H.finC)

/-! ## `init`

Registers: `rbx` = `inner`, `r12` = `outer`, `r15` = `scratch`, `rbp` =
`key`, `r13` = `key_len`, `r14` = the byte index. `K₀ ⊕ ipad` is at
`scratch + buf`, and `K₀ ⊕ opad` right after it. -/

/-- The key bytes, XORed with `ipad` and `opad` into the two blocks. -/
def keyLoop : Prog isa :=
  .loop (.block [.movzx8 .rax (byteAt .rbp 0), .mov32 .rcx (.reg .rax),
    .alu32 .xor .rax (.imm 0x36), .store8 (byteAt .r15 H.buf) .rax, .alu32 .xor .rcx (.imm 0x5c),
    .store8 (byteAt .r15 (H.buf + H.B)) .rcx, .alu .add .r14 (.imm 1),
    .alu .cmp .r14 (.reg .r13)]) .ne

/-- The zero bytes after the key, XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block [.store8 (byteAt .r15 H.buf) .rax, .store8 (byteAt .r15 (H.buf + H.B)) .rcx,
    .alu .add .r14 (.imm 1), .alu .cmp .r14 (.imm (BitVec.ofNat 32 H.B))]) .ne

def initPrologue : List Instr :=
  H.save ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .r8),
    .mov .rbp (.reg .rdx), .mov .r13 (.reg .rcx), .mov32 .r14 (.imm 0), .alu .test .r13 (.reg .r13)]

/-- `K₀ ⊕ ipad` and `K₀ ⊕ opad` into `scratch`: the part of `init` before its calls. -/
def initKeys : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (.ite .e (.block []) H.keyLoop)
  (.seq (.block [.mov32 .rax (.imm 0x36), .mov32 .rcx (.imm 0x5c),
      .alu .cmp .r14 (.imm (BitVec.ofNat 32 H.B))])
    (.ite .e (.block []) H.padLoop)))

def init : Prog isa :=
  .seq H.initKeys
  (.seq (H.callInit .rbx)
  (.seq (H.callUpd [.mov .rdi (.reg .rbx)] 0 H.buf H.B)
  (.seq (H.callInit .r12)
  (.seq (H.callUpd [.mov .rdi (.reg .r12)] 0 (H.buf + H.B) H.B)
    (.block H.restore)))))

/-! ## `init` for a key of any length

`initAny` compares `key_len` with the block size. A longer key is hashed
first (`hashKey`): `init`, `update` and `finalize` on a streaming state at
`scratch + ext`, after `init`'s buffers, with the digest written after the
state; then `init` runs on that digest, `D` bytes. `hashKey` keeps its
variables where `init` does (`rbx` = `inner`, `r12` = `outer`, `r15` =
`scratch`, `rbp` = `key`, `r13` = `key_len`), saving and restoring our
caller's registers in the same place. -/

/-- Where the streaming state of a long key is: after `init`'s buffers,
rounded up to a whole word. Its digest follows it. -/
def ext : Nat := 8 * ((H.buf + 2 * H.B + 7) / 8)

def hashKey : Prog isa :=
  .seq (.block (H.save ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .r8),
      .mov .rbp (.reg .rdx), .mov .r13 (.reg .rcx)]))
  (.seq (H.callInit' H.ext)
  (.seq (.block (scr .rdi H.ext ++ [.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbp), .mov .rcx (.reg .r13),
      .mov .r8 (.reg .r15)]))
  (.seq (.call H.updN H.updC)
  (.seq (.block (scr .rdi H.ext ++ [.mov .rsi (.reg .r13)] ++ scr .rdx (H.ext + H.S) ++
      [.mov .rcx (.reg .r15)]))
  (.seq (.call H.finN H.finC)
    (.block ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .r12), .mov .r8 (.reg .r15)] ++
      scr .rdx (H.ext + H.S) ++ [.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] ++ H.restore)))))))

def initAny : Prog isa :=
  .seq (.block [.alu .cmp .rcx (.imm (BitVec.ofNat 32 (H.B + 1)))])
  (.seq (.ite .b (.block []) H.hashKey) H.init)

/-! ## `finalize`

Registers: `rbx` = `inner`, `r12` = `outer`, `r13` = `out`, `r15` =
`scratch`, `r14` = the byte index. The digests are written to
`scratch + buf`. -/

def finPrologue : List Instr :=
  H.save ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r13 (.reg .rcx),
    .mov .r15 (.reg .r8)]

def finalize : Prog isa :=
  .seq (.block H.finPrologue)
  (.seq (H.callFin [] [.mov .rsi (.reg .rdx)] H.buf)
  (.seq (copy .r12 0 .rbx 0 H.S)
  (.seq (H.callUpd [.mov .rdi (.reg .rbx)] H.B H.buf H.D)
  (.seq (H.callFin [.mov .rdi (.reg .rbx)] [.mov32 .rsi (.imm (BitVec.ofNat 32 (H.B + H.D)))] H.buf)
  (.seq (copy .r15 H.buf .r13 0 H.D)
    (.block H.restore))))))

end Hash

end VG.Impl.Hmac.Generic.X86_64
