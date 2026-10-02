import VerifiedGarbage.TCB.Arm.Isa

/-!
# HMAC over any streaming hash function: 32-bit ARM implementation

HMAC's `init`, as on x86-64 and AArch64 (`VG.Impl.Hmac.Generic.X86_64`,
`VG.Impl.Hmac.Generic.AArch64`), once for every streaming hash function whose
`init` and `update` it calls (`Hash`):

* `init(inner = r0, outer = r1, key = r2, key_len = r3, scratch = [sp])`
  writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` into `scratch`, then makes the inner
  state absorb the first and the outer state the second, with `init` and
  `update`.

HMAC's `finalize` and PBKDF2's `iterate` for the Merkle–Damgård hash
functions call their compression function instead
(`VG.Impl.Pbkdf2.Md.Arm`), and use the helpers here (`saved`, `buf`,
`callFin`, `scrAt`), as does the whole of PBKDF2 (`VG.Impl.Pbkdf2.Whole.Arm`,
also `copy`).

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
has no register-offset addressing, so the byte loops
address byte `r8` of a buffer as `[r2, #off]` with `r2 = base + r8`, and
count down in `r9` (`subs` and `bne`). Offsets into `scratch` that an ARM
instruction cannot encode as an immediate are formed with `movw r12` and an
`add`.
-/

namespace VG.Impl.Hmac.Generic.Arm

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

/-- A call of `update` on the state at `r0` (set by `st`, first), with the
count `count` and the `len` bytes at `scratch + o`: `data`, `len` and
`scratch` are pushed. -/
def callUpd (st : List Instr) (count o len : Nat) : Prog isa :=
  .seq (.block (st ++ scrAt .r1 o ++ [.movw .r7 (BitVec.ofNat 16 len), .mov .r10 (.reg .r11),
      .movw .r2 (BitVec.ofNat 16 count), .mov .r3 (.imm 0)]))
    (.frame (.push [.r1, .r7, .r10, .r12]) (.call H.updN H.updC) (.pop .r1 16))

/-- A call of `finalize` on the state at `r0` (set by `st`, first), with the
count in `r2:r3` (set by `count`) and the digest to `scratch + o`: `out` and
`scratch` are pushed. -/
def callFin (st count : List Instr) (o : Nat) : Prog isa :=
  .seq (.block (st ++ count ++ scrAt .r1 o ++ [.mov .r12 (.reg .r11)]))
    (.frame (.push [.r1, .r12]) (.call H.finN H.finC) (.pop .r1 8))

/-! ## `init`

Registers: `r4` = `inner`, `r5` = `outer`, `r6` = `key`, `r11` = `scratch`,
`r8` = the byte index, `r9` = the bytes left. `K₀ ⊕ ipad` is at
`scratch + buf`, and `K₀ ⊕ opad` right after it. -/

/-- The key bytes, XORed with `ipad` and `opad` into the two blocks. -/
def keyLoop : Prog isa :=
  .loop (.block [.dp .add .r2 .r6 (.reg .r8), .ldrb .r12 .r2 0, .dp .eor .r1 .r12 (.imm 0x36),
    .dp .add .r2 .r11 (.reg .r8), .strb .r1 .r2 H.buf, .dp .eor .r1 .r12 (.imm 0x5c),
    .strb .r1 .r2 (H.buf + H.B), .dp .add .r8 .r8 (.imm 1), .subs .r9 .r9 (.imm 1)]) .ne

/-- The zero bytes after the key, XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block [.dp .add .r2 .r11 (.reg .r8), .mov .r1 (.imm 0x36), .strb .r1 .r2 H.buf,
    .mov .r1 (.imm 0x5c), .strb .r1 .r2 (H.buf + H.B), .dp .add .r8 .r8 (.imm 1),
    .subs .r9 .r9 (.imm 1)]) .ne

def initPrologue : List Instr :=
  [.ldrSp .r12 0] ++ H.save ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
    .mov .r11 (.reg .r12), .mov .r8 (.imm 0), .mov .r9 (.reg .r3), .cmp .r9 (.imm 0)]

/-- `K₀ ⊕ ipad` and `K₀ ⊕ opad` into `scratch`: the part of `init` before its calls. -/
def initKeys : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (.ite .eq (.block []) H.keyLoop)
  (.seq (.block [.movw .r9 (BitVec.ofNat 16 H.B), .subs .r9 .r9 (.reg .r8)])
    (.ite .eq (.block []) H.padLoop)))

def init : Prog isa :=
  .seq H.initKeys
  (.seq (H.callInit .r4)
  (.seq (H.callUpd [.mov .r0 (.reg .r4)] 0 H.buf H.B)
  (.seq (H.callInit .r5)
  (.seq (H.callUpd [.mov .r0 (.reg .r5)] 0 (H.buf + H.B) H.B)
    (.block H.restore)))))

end Hash

end VG.Impl.Hmac.Generic.Arm
