import VerifiedGarbage.TCB.X86.Isa

/-!
# Calls of a streaming hash function: x86 (32-bit)

What the code over a hash function's streaming functions shares: HMAC's
`init` and `finalize` and PBKDF2's `iterate` over the Merkle–Damgård hash
functions (`VG.Impl.Pbkdf2.Md.X86`), and the whole of PBKDF2
(`VG.Impl.Pbkdf2.Whole.X86`). A `Hash` is a streaming hash function's
`init`, `update` and `finalize`, with their sizes and names; `callInit` and
`callFin` call `init` and `finalize`; `save` and `restore` keep our caller's
registers in `scratch` (`saved`); `finPrologue` and `count1` start HMAC's
`finalize`; and `copy` copies bytes. Every argument is on the stack (cdecl).

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
index registers, so `copy` addresses byte `ecx` of a buffer at
`base + off` as `[eax + off]` (or `[edx + off]`), with `eax = base + ecx`
computed just before the access.
-/

namespace VG.Impl.Pbkdf2.Stream.X86

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

/-- A call of `finalize` on the state at `st` (set by `pre`, first), with the
count in `eax` (low word) and `ecx` (high word), set by `count`, and the
digest to `scratch + o` (in `edx`). -/
def callFin (pre count : List Instr) (st : Reg) (o : Nat) : Prog isa :=
  .seq (.block (pre ++ count ++ scr .edx o))
    (.frame (.push [.ebp, .edx, .ecx, .eax, st]) (.call H.finN H.finC) (.pop .eax 5))

/-! ## The start of `finalize`

Registers: `ebx` = `inner`, `esi` = `outer`, `edi` = `out`, `ebp` =
`scratch`. The inner digest is written to `scratch + buf`. -/

def finPrologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 24))] ++ H.save ++ [.mov .ebp (.reg .eax), .mov .ebx (.mem (at_ .esp 4)),
    .mov .esi (.mem (at_ .esp 8)), .mov .edi (.mem (at_ .esp 20))]

/-- Our `count` argument, as `finalize`'s. -/
def count1 : List Instr := [.mov .eax (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 16))]

end Hash

end VG.Impl.Pbkdf2.Stream.X86
