import VerifiedGarbage.TCB.X86.Isa

/-!
# HMAC over any streaming hash function: x86 (32-bit) implementation

The same algorithm as on the other targets (`VG.Impl.Hmac.Generic.Arm`), once
for every streaming hash function whose `init`, `update` and `finalize` it
calls (`Hash`). Every argument is on the stack (cdecl).

* `init(inner, outer, key, key_len, scratch)` writes `K₀ ⊕ ipad` and
  `K₀ ⊕ opad` into `scratch`, then makes the inner state absorb the first
  and the outer state the second, with `init` and `update`.
* `finalize(inner, outer, count, out, scratch)` starts with `finPrologue`
  and a call of the streaming `finalize` on the inner state (`callFin`,
  `count1`); the rest of it, the outer hash, is one call of the compression
  function on a block laid out in `scratch`, written over the hash function's
  compression function (`VG.Impl.Pbkdf2.Md.X86`).

Each call passes its arguments in a frame of their own, pushed last to
first (`push`), which the pop loads into `eax` when the call returns: every
argument is set in a register before the push, so a frame holds only the
call. `update` takes six words (`state`, the low and high words of `count`,
`data`, `len`, `scratch`) and `finalize` five; with the return address and
the 20 bytes of stack below it that `update` and `finalize` use, the
functions use 48 bytes of stack.

`scratch` holds the working space of the functions we call (`8 W` bytes,
the largest of theirs); then our caller's `ebx`, `esi`, `edi` and `ebp`
(`saved`); then our buffers. The functions we call preserve those four
registers, so our variables live there; `ebp` is always `scratch`, and our
own arguments are read from the stack again when needed. The model has no
index registers, so the byte loops address byte `ecx` of a buffer at
`base + off` as `[eax + off]` (or `[edx + off]`), with `eax = base + ecx`
computed just before the access.
-/

namespace VG.Impl.Hmac.Generic.X86

open VG.X86

/-- `[b + d]`. -/
def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- A streaming hash function's x86 functions, as we call them: the block
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

/-- `n > 0` bytes copied from `[src + so]` to `[dst + d]`, with `ecx` the
index and `eax` and `edx` temporaries. -/
def copy (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)])
    (.loop (.block [.mov .eax (.reg src), .alu .add .eax (.reg .ecx), .movzx8 .edx (at_ .eax so),
      .mov .eax (.reg dst), .alu .add .eax (.reg .ecx), .store8 (at_ .eax d) .dl,
      .alu .add .ecx (.imm 1), .alu .cmp .ecx (.imm (BitVec.ofNat 32 n))]) .ne)

/-- `d ← ebp + o`: an address in `scratch`. -/
def scr (d : Reg) (o : Nat) : List Instr := [.mov d (.reg .ebp), .alu .add d (.imm (BitVec.ofNat 32 o))]

namespace Hash

variable (H : Hash)

/-- Where our caller's registers are saved in `scratch`: after the working
space of the functions we call. -/
def saved : List (Reg × Nat) :=
  [(.ebx, 8 * H.W), (.esi, 8 * H.W + 4), (.edi, 8 * H.W + 8), (.ebp, 8 * H.W + 12)]

/-- Where our buffers start in `scratch`. -/
def buf : Nat := 8 * H.W + 16

/-- Saving our caller's registers, with `scratch` in `eax`. -/
def save : List Instr := H.saved.map fun (r, d) => .store (at_ .eax d) r

/-- Restoring them, with `scratch` in `ebp`. -/
def restore : List Instr := .mov .eax (.reg .ebp) :: H.saved.map fun (r, d) => .mov r (.mem (at_ .eax d))

/-- A call of `init` on the state at `st`, in a frame of its argument. -/
def callInit (st : Reg) : Prog isa :=
  .frame (.push [st]) (.call H.initN H.initC) (.pop .eax 1)

/-- A call of `update` on the state at `st` (set by `pre`, first), with the
count `count` (in `lo`, and `eax = 0` its high word) and the `len` bytes at
`scratch + o` (in `edx`, and `ecx = len`). -/
def callUpd (pre : List Instr) (st lo : Reg) (count o len : Nat) : Prog isa :=
  .seq (.block (pre ++ [.mov .eax (.imm 0), .mov lo (.imm (BitVec.ofNat 32 count)),
      .mov .ecx (.imm (BitVec.ofNat 32 len))] ++ scr .edx o))
    (.frame (.push [.ebp, .ecx, .edx, .eax, lo, st]) (.call H.updN H.updC) (.pop .eax 6))

/-- A call of `finalize` on the state at `st` (set by `pre`, first), with the
count in `eax` (low word) and `ecx` (high word), set by `count`, and the
digest to `scratch + o` (in `edx`). -/
def callFin (pre count : List Instr) (st : Reg) (o : Nat) : Prog isa :=
  .seq (.block (pre ++ count ++ scr .edx o))
    (.frame (.push [.ebp, .edx, .ecx, .eax, st]) (.call H.finN H.finC) (.pop .eax 5))

/-! ## `init`

Registers: `ebp` = `scratch`, `esi` = `key`, `edi` = `key_len`, `ebx` = the
byte index while the keys are written; then `ebx` = `inner` and `esi` =
`outer`, and `edi` passes `update` the low word of its count. `K₀ ⊕ ipad`
is at `scratch + buf`, and `K₀ ⊕ opad` right after it. -/

/-- The key bytes, XORed with `ipad` and `opad` into the two blocks. -/
def keyLoop : Prog isa :=
  .loop (.block [.mov .eax (.reg .esi), .alu .add .eax (.reg .ebx), .movzx8 .eax (at_ .eax 0),
    .mov .ecx (.reg .eax), .alu .xor .eax (.imm 0x36), .mov .edx (.reg .ebp), .alu .add .edx (.reg .ebx),
    .store8 (at_ .edx H.buf) .al, .alu .xor .ecx (.imm 0x5c), .store8 (at_ .edx (H.buf + H.B)) .cl,
    .alu .add .ebx (.imm 1), .alu .cmp .ebx (.reg .edi)]) .ne

/-- The zero bytes after the key, XORed likewise (`ipad` in `eax`, `opad` in
`ecx`). -/
def padLoop : Prog isa :=
  .loop (.block [.mov .edx (.reg .ebp), .alu .add .edx (.reg .ebx), .store8 (at_ .edx H.buf) .al,
    .store8 (at_ .edx (H.buf + H.B)) .cl, .alu .add .ebx (.imm 1),
    .alu .cmp .ebx (.imm (BitVec.ofNat 32 H.B))]) .ne

def initPrologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ H.save ++ [.mov .ebp (.reg .eax), .mov .esi (.mem (at_ .esp 12)),
    .mov .edi (.mem (at_ .esp 16)), .mov .ebx (.imm 0), .alu .test .edi (.reg .edi)]

/-- `K₀ ⊕ ipad` and `K₀ ⊕ opad` into `scratch`: the part of `init` before its calls. -/
def initKeys : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (.ite .e (.block []) H.keyLoop)
  (.seq (.block [.mov .eax (.imm 0x36), .mov .ecx (.imm 0x5c), .alu .cmp .ebx (.imm (BitVec.ofNat 32 H.B))])
    (.ite .e (.block []) H.padLoop)))

/-- `inner` and `outer`, from the stack. -/
def initStates : List Instr := [.mov .ebx (.mem (at_ .esp 4)), .mov .esi (.mem (at_ .esp 8))]

def init : Prog isa :=
  .seq H.initKeys
  (.seq (.block initStates)
  (.seq (H.callInit .ebx)
  (.seq (H.callUpd [] .ebx .edi 0 H.buf H.B)
  (.seq (H.callInit .esi)
  (.seq (H.callUpd [] .esi .edi 0 (H.buf + H.B) H.B)
    (.block H.restore))))))

/-! ## The start of `finalize`

Registers: `ebx` = `inner`, `esi` = `outer`, `edi` = `out`, `ebp` =
`scratch`. The inner digest is written to `scratch + buf`. -/

def finPrologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 24))] ++ H.save ++ [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
    .mov .esi (.mem (at_ .esp 8)), .mov .edi (.mem (at_ .esp 20))]

/-- Our `count` argument, as `finalize`'s. -/
def count1 : List Instr := [.mov .eax (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 16))]

end Hash

end VG.Impl.Hmac.Generic.X86
