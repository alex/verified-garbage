import VerifiedGarbage.TCB.Arm.Isa

/-!
# Calls of a streaming hash function: 32-bit ARM

What the code over a hash function's streaming functions shares: HMAC's
`init` and `finalize` and PBKDF2's `iterate` over the Merkle–Damgård hash
functions (`VG.Impl.Pbkdf2.Md.Arm`), and the whole of PBKDF2
(`VG.Impl.Pbkdf2.Whole.Arm`). A `Hash` is a streaming hash function's
`init`, `update` and `finalize`, with their sizes and names; `callInit` and
`callFin` call `init` and `finalize`; `save` and `restore` keep our caller's
registers and our return address in `scratch` (`saved`); `scrAt` forms an
address in `scratch`; and `copy` copies bytes.

`update` and `finalize` take some of their arguments on the stack: each call
of them is in a frame that pushes those (`push {r1, r7, r10, r12}` for
`update`'s `data`, `len` and `scratch`, and a word of padding, which keeps
the stack pointer 8-byte aligned; `push {r1, r12}` for `finalize`'s `out` and
`scratch`), and whose pop loads the first back into `r1`. Every argument is
set before the push, so a frame holds only the call. So the functions use 16
bytes of stack.

`scratch` holds the working space of the functions we call (`8 W` bytes, the
largest of theirs); then our caller's registers that we use and our return
address (`saved`), which each call replaces; then our buffers. The functions
we call preserve `r4`–`r11`, so our variables live there; `r11` is always
`scratch`, and `r7` and `r10` pass `update`'s stack arguments. The model
has no register-offset addressing, so `copy` addresses byte `r8` of a buffer
as `[r2, #off]` with `r2 = base + r8`, and counts down in `r9` (`subs` and
`bne`). Offsets into `scratch` that an ARM
instruction cannot encode as an immediate are formed with `movw r12` and an
`add`.
-/

namespace VG.Impl.Pbkdf2.Stream.Arm

open VG.Arm

/-- A streaming hash function's 32-bit ARM functions, as we call them: the
block size `B`, the sizes of the streaming state (`S`), of the digest (`D`)
and of what `finalize` writes (`F`, at least `D`), the words of working space
of `update` and `finalize` (`W`), and the three functions, with their names. -/
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

/-- `d ← scratch + o`, for any `o < 2¹⁶`. -/
def scrAt (d : Reg) (o : Nat) : List Instr := [.movw .r12 (BitVec.ofNat 16 o), .dp .add d .r11 (.reg .r12)]

/-- `n > 0` bytes copied from `[src + so]` to `[dst + d]`, with `r8` the
index and `r9` the bytes left. -/
def copy (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) : Prog isa :=
  .seq (.block [.mov .r8 (.imm 0), .movw .r9 (BitVec.ofNat 16 n)])
    (.loop (.block [.dp .add .r2 src (.reg .r8), .ldrb .r12 .r2 so, .dp .add .r2 dst (.reg .r8),
      .strb .r12 .r2 d, .dp .add .r8 .r8 (.imm 1), .subs .r9 .r9 (.imm 1)]) .ne)

namespace Hash

variable (H : Hash)

/-- Where our caller's registers and our return address are saved in
`scratch`: after the working space of the functions we call (`r11`, which
holds `scratch`, last). -/
def saved : List (Reg × Nat) :=
  [(.r4, 8 * H.W), (.r5, 8 * H.W + 4), (.r6, 8 * H.W + 8), (.r7, 8 * H.W + 12), (.r8, 8 * H.W + 16),
    (.r9, 8 * H.W + 20), (.r10, 8 * H.W + 24), (.lr, 8 * H.W + 28), (.r11, 8 * H.W + 32)]

/-- Where our buffers start in `scratch`. -/
def buf : Nat := 8 * H.W + 36

/-- Saving them, with `scratch` in `r12`. -/
def save : List Instr := H.saved.map fun (r, d) => .str r .r12 d

/-- Restoring them, with `scratch` in `r11` (restored last). -/
def restore : List Instr := H.saved.map fun (r, d) => .ldr r .r11 d

/-- A call of `init` on the state at `st`. -/
def callInit (st : Reg) : Prog isa :=
  .seq (.block [.mov .r0 (.reg st)]) (.call H.initN H.initC)

/-- A call of `finalize` on the state at `r0` (set by `st`, first), with the
count in `r2:r3` (set by `count`) and the digest to `scratch + o`: `out` and
`scratch` are pushed. -/
def callFin (st count : List Instr) (o : Nat) : Prog isa :=
  .seq (.block (st ++ count ++ scrAt .r1 o ++ [.mov .r12 (.reg .r11)]))
    (.frame (.push [.r1, .r12]) (.call H.finN H.finC) (.pop .r1 8))

end Hash

end VG.Impl.Pbkdf2.Stream.Arm
