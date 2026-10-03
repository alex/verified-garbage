import VerifiedGarbage.Impl.Pbkdf2.Stream.Arm

/-!
# PBKDF2-HMAC over any streaming hash function: 32-bit ARM implementation of the whole derivation

`pbkdf2(password = r0, password_len = r1, salt = r2, salt_len = r3,
c = [sp], out = [sp, #4], out_len = [sp, #8], scratch = [sp, #12])`
computes PBKDF2-HMAC (RFC 8018 §5.2) from the verified functions of one hash
function (`Fns`), as on x86 (`VG.Impl.Pbkdf2.Whole.X86`): the key is the
password, or its digest if it is longer than a block; HMAC's `init` makes
the key's inner and outer states, and the inner one is copied and absorbs
the salt once; each block `i` of the output copies that state, absorbs
`INT (i)` into it and computes `U₁` with HMAC's `finalize`; `T` starts as
`U₁`, `iterate` runs the other `c - 1` steps, and as much of `T` as the
output still needs is copied to `out`.

`scratch` starts with the working space of the functions we call (`8 W`
bytes); then our caller's registers and our return address (as in HMAC's
code, `VG.Impl.Pbkdf2.Stream.Arm.Hash.saved`), the key's two states, the
salted inner state, a working state, `U`, `T`, the hashed password (the `F`
bytes `finalize` writes) and `INT (i)`. The functions we call preserve
`r4`–`r11`: `r11` is always `scratch`, `r5` and `r6` the salt and its
length, `r8` and `r9` the password and its length (until the key is made),
and, in the loop over the blocks, `r4` the number of bytes of output written;
`r7` and `r10` pass `update`'s stack arguments, which a frame pushes
(`push {r1, r7, r10, r12}`, as in HMAC's code); `finalize`'s are pushed with
`push {r1, r12}`, HMAC's `finalize`'s with `push {r10, r12}`, and the one
of HMAC's `init` and of `iterate` with `push {r12, lr}`, so that the stack
pointer stays 8-byte aligned. `c`, `out` and `out_len` are read from the
stack whenever they are needed. `INT (i)` is kept in `scratch`, big-endian,
and incremented in place (`rev`). The model's branches test only `Z`, so a
comparison `x ≥ k` is made into a flag with `subs` and `adc` (the carry).
Every address and branch depends only on the pointers, the lengths and `c`.
-/

namespace VG.Impl.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Stream.Arm (Hash copy scrAt)

/-- The functions PBKDF2 calls, for one hash function: its streaming
functions (`H`, with their sizes), the words of working space every function
we call gets (`W`, the hash function's `VG.Spec.Hmac.Instance.scratch`), and
HMAC's `init` and `finalize` and PBKDF2's `iterate`, with their names. -/
structure Fns where
  H : Hash
  W : Nat
  hiN : String
  hiC : Prog isa
  hfN : String
  hfC : Prog isa
  itN : String
  itC : Prog isa

namespace Fns

variable (F : Fns)

/-- The layout of the start of `scratch`, as in HMAC's code: the working
space of the functions we call, then our caller's registers (`L.saved`),
then our buffers (from `L.buf`). -/
def L : Hash := { F.H with W := F.W }

/-- The key's inner and outer states, the salted inner state and the working state. -/
def st0O : Nat := F.L.buf
def st1O : Nat := F.st0O + F.H.S
def stSO : Nat := F.st1O + F.H.S
def stWO : Nat := F.stSO + F.H.S

/-- `U`, `T`, the hashed password and `INT (i)`. -/
def uO : Nat := F.stWO + F.H.S
def tO : Nat := F.uO + F.H.D
def hkO : Nat := F.tO + F.H.D
def intO : Nat := F.hkO + F.H.F

/-- Our caller's registers into `scratch`, which `r11` then holds; the
arguments into the registers that keep them. -/
def prologue : List Instr :=
  [.ldrSp .r12 12] ++ F.L.save ++
    [.mov .r11 (.reg .r12), .mov .r8 (.reg .r0), .mov .r9 (.reg .r1), .mov .r5 (.reg .r2), .mov .r6 (.reg .r3)]

/-- `Z` is whether `password_len < B + 1`. -/
def cmpPw : List Instr :=
  [.subs .r12 .r9 (.imm (BitVec.ofNat 32 (F.H.B + 1))), .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0),
    .cmp .r12 (.imm 0)]

/-- A password longer than a block: its digest is the key. -/
def hashKey : Prog isa :=
  .seq (.block (scrAt .r4 F.stWO))
  (.seq (F.H.callInit .r4)
  (.seq (.block [.mov .r0 (.reg .r4), .mov .r1 (.reg .r8), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
      .mov .r2 (.imm 0), .mov .r3 (.imm 0)])
  (.seq (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
  (.seq (.block ([.mov .r0 (.reg .r4)] ++ scrAt .r1 F.hkO ++ [.mov .r12 (.reg .r11), .mov .r2 (.reg .r9),
      .mov .r3 (.imm 0)]))
  (.seq (.frame (.push [.r1, .r12]) (.call F.H.finN F.H.finC) (.pop .r1 8))
    (.block (scrAt .r2 F.hkO ++ [.movw .r3 (BitVec.ofNat 16 F.H.D)])))))))

/-- The key, at `r2`, of `r3` bytes. -/
def key : Prog isa :=
  .seq (.block F.cmpPw) (.ite .eq (.block [.mov .r2 (.reg .r8), .mov .r3 (.reg .r9)]) F.hashKey)

/-- HMAC's `init`'s arguments: the key's states and `scratch`. -/
def initArgs : List Instr := scrAt .r0 F.st0O ++ scrAt .r1 F.st1O ++ [.mov .r12 (.reg .r11)]

/-- `update`'s arguments for the salt. -/
def saltArgs : List Instr :=
  scrAt .r0 F.stSO ++ [.mov .r1 (.reg .r5), .mov .r7 (.reg .r6), .mov .r10 (.reg .r11),
    .movw .r2 (BitVec.ofNat 16 F.H.B), .mov .r3 (.imm 0)]

/-- HMAC's states for the key, and the inner one after the salt. -/
def setup : Prog isa :=
  .seq (.block F.initArgs)
  (.seq (.frame (.push [.r12, .lr]) (.call F.hiN F.hiC) (.pop .r12 8))
  (.seq (copy .r11 F.st0O .r11 F.stSO F.H.S)
  (.seq (.block F.saltArgs)
    (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16)))))

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
def loopInit : List Instr :=
  [.mov .r12 (.imm 1), .rev .r12 .r12, .str .r12 .r11 F.intO, .mov .r4 (.imm 0), .ldrSp .r12 8,
    .cmp .r12 (.imm 0)]

/-- `update`'s arguments: the working state, `INT (i)`, and the bytes absorbed. -/
def updArgs : List Instr :=
  scrAt .r0 F.stWO ++ scrAt .r1 F.intO ++ [.mov .r7 (.imm 4), .mov .r10 (.reg .r11),
    .dp .add .r2 .r6 (.imm (BitVec.ofNat 32 F.H.B)), .mov .r3 (.imm 0)]

/-- HMAC's `finalize`'s arguments: the working state, the outer state, the
bytes absorbed, `U` and `scratch`. -/
def finArgs : List Instr :=
  scrAt .r0 F.stWO ++ scrAt .r1 F.st1O ++ scrAt .r10 F.uO ++ [.mov .r12 (.reg .r11),
    .dp .add .r2 .r6 (.imm (BitVec.ofNat 32 (F.H.B + 4))), .mov .r3 (.imm 0)]

/-- `iterate`'s arguments: the key's states, `U`, `c - 1`, `T` and `scratch`. -/
def iterArgs : List Instr :=
  scrAt .r0 F.st0O ++ scrAt .r1 F.uO ++ scrAt .r3 F.tO ++ [.ldrSp .r2 0, .dp .sub .r2 .r2 (.imm 1),
    .mov .r12 (.reg .r11)]

/-- The bytes of `T` the output still needs, `min (out_len - r4, D)`, in `r9`. -/
def outLen : Prog isa :=
  .seq (.block [.ldrSp .r12 8, .dp .sub .r9 .r12 (.reg .r4), .subs .r12 .r9 (.imm (BitVec.ofNat 32 F.H.D)),
      .mov .r12 (.imm 0), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)])
    (.ite .eq (.block []) (.block [.movw .r9 (BitVec.ofNat 16 F.H.D)]))

/-- The loop copying `r9` bytes of `T` to `out + r4`, with `r8` the index. -/
def outLoop : Prog isa :=
  .seq (.block [.ldrSp .r10 4, .dp .add .r10 .r10 (.reg .r4), .mov .r8 (.imm 0)])
    (.loop (.block [.dp .add .r2 .r11 (.reg .r8), .ldrb .r12 .r2 F.tO, .dp .add .r2 .r10 (.reg .r8),
      .strb .r12 .r2 0, .dp .add .r8 .r8 (.imm 1), .subs .r9 .r9 (.imm 1)]) .ne)

/-- The bytes written, the next `INT (i)`, and whether the output is complete. -/
def advance : List Instr :=
  [.dp .add .r4 .r4 (.reg .r8), .ldr .r12 .r11 F.intO, .rev .r12 .r12, .dp .add .r12 .r12 (.imm 1),
    .rev .r12 .r12, .str .r12 .r11 F.intO, .ldrSp .r12 8, .cmp .r4 (.reg .r12)]

/-- One block of the output. -/
def block : Prog isa :=
  .seq (copy .r11 F.stSO .r11 F.stWO F.H.S)
  (.seq (.block F.updArgs)
  (.seq (.frame (.push [.r1, .r7, .r10, .r12]) (.call F.H.updN F.H.updC) (.pop .r1 16))
  (.seq (.block F.finArgs)
  (.seq (.frame (.push [.r10, .r12]) (.call F.hfN F.hfC) (.pop .r12 8))
  (.seq (copy .r11 F.uO .r11 F.tO F.H.D)
  (.seq (.block F.iterArgs)
  (.seq (.frame (.push [.r12, .lr]) (.call F.itN F.itC) (.pop .r12 8))
  (.seq F.outLen
  (.seq F.outLoop
    (.block F.advance))))))))))

def pbkdf2 : Prog isa :=
  .seq (.block F.prologue)
  (.seq F.key
  (.seq F.setup
  (.seq (.block F.loopInit)
  (.seq (.ite .eq (.block []) (.loop F.block .ne))
    (.block F.L.restore)))))

end Fns

end VG.Impl.Pbkdf2.Whole.Arm
