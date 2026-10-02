import VerifiedGarbage.Impl.Hmac.Generic.X86

/-!
# PBKDF2-HMAC over any streaming hash function: x86 (32-bit) implementation of the whole derivation

`pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`,
every argument on the stack (cdecl), computes PBKDF2-HMAC (RFC 8018 §5.2)
from the verified functions of one hash function (`Fns`): its streaming
`init`, `update` and `finalize`, HMAC's `init` and `finalize`, and PBKDF2's
`iterate`. The same algorithm as on x86-64 (`VG.Impl.Pbkdf2.Md.X86_64`):

* the key is the password, or its digest if it is longer than a block
  (`init`, `update`, `finalize` into `scratch`);
* HMAC's `init` makes the key's inner and outer streaming states, one after
  the other in `scratch` (as `iterate` takes them), and the inner one is
  copied and absorbs the salt once (`update`);
* each block `i` of the output copies that state, absorbs `INT (i)` into it
  (`update`) and computes `U₁` with HMAC's `finalize`; `T` starts as `U₁`,
  `iterate` runs the other `c - 1` steps, and as much of `T` as the output
  still needs is copied to `out`.

`scratch` starts with the working space of the functions we call (`8 W`
bytes); then come our caller's `ebx`, `esi`, `edi` and `ebp` (as in HMAC's
code, `VG.Impl.Hmac.Generic.X86.Hash.saved`), the key's two states, the
salted inner state, a working state, `U`, `T`, the hashed password (the `F`
bytes `finalize` writes) and `INT (i)`. Every call passes its arguments in a
frame of their own, pushed last to first, which the pop loads into `eax`.
Our arguments are read from the stack whenever they are needed. `ebp` is
always `scratch`; in the loop over the blocks, `ebx` is the number of bytes
of output written, and `INT (i)` is kept in `scratch`, big-endian, and
incremented in place. The functions we call preserve `ebx`, `esi`, `edi`
and `ebp`; `esi` and `edi` pass arguments. Every address and branch depends
only on the pointers, the lengths and `c`.
-/

namespace VG.Impl.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash copy scr at_)

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

/-- Argument `i`, on the stack. -/
def argM (i : Nat) : Src := .mem (at_ .esp (4 + 4 * i))

/-- Our caller's registers into `scratch`, which `ebp` then holds. -/
def prologue : List Instr := [.mov .eax (argM 7)] ++ F.L.save ++ [.mov .ebp (.reg .eax)]

/-- `password_len`, compared with `B + 1`. -/
def cmpPw : List Instr := [.mov .ecx (argM 1), .alu .cmp .ecx (.imm (BitVec.ofNat 32 (F.H.B + 1)))]

/-- A password longer than a block: its digest is the key. -/
def hashKey : Prog isa :=
  .seq (.block (scr .edi F.stWO))
  (.seq (F.H.callInit .edi)
  (.seq (.block [.mov .eax (.imm 0), .mov .esi (.imm 0), .mov .ecx (argM 1), .mov .edx (argM 0)])
  (.seq (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
  (.seq (.block ([.mov .eax (argM 1), .mov .ecx (.imm 0)] ++ scr .edx F.hkO))
  (.seq (.frame (.push [.ebp, .edx, .ecx, .eax, .edi]) (.call F.H.finN F.H.finC) (.pop .eax 5))
    (.block (scr .edx F.hkO ++ [.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))])))))))

/-- The key, at `edx`, of `ecx` bytes. -/
def key : Prog isa :=
  .seq (.block F.cmpPw) (.ite .ae F.hashKey (.block [.mov .edx (argM 0)]))

/-- HMAC's states for the key, and the inner one after the salt. -/
def setup : Prog isa :=
  .seq (.block (scr .edi F.st0O ++ scr .esi F.st1O))
  (.seq (.frame (.push [.ebp, .ecx, .edx, .esi, .edi]) (.call F.hiN F.hiC) (.pop .eax 5))
  (.seq (copy .ebp F.st0O .ebp F.stSO F.H.S)
  (.seq (.block (scr .edi F.stSO ++ [.mov .eax (.imm 0), .mov .esi (.imm (BitVec.ofNat 32 F.H.B)),
      .mov .ecx (argM 3), .mov .edx (argM 2)]))
    (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6)))))

/-- `INT (1)`, no bytes written, and whether `out_len` is 0. -/
def loopInit : List Instr :=
  [.mov .eax (.imm 1), .bswap .eax, .store (at_ .ebp F.intO) .eax, .mov .ebx (.imm 0), .mov .ecx (argM 6),
    .alu .test .ecx (.reg .ecx)]

/-- `update`'s arguments: the working state, the bytes it has absorbed, and `INT (i)`. -/
def updArgs : List Instr :=
  scr .edi F.stWO ++ [.mov .esi (argM 3), .alu .add .esi (.imm (BitVec.ofNat 32 F.H.B)), .mov .eax (.imm 0),
    .mov .ecx (.imm 4)] ++ scr .edx F.intO

/-- HMAC's `finalize`'s arguments: the working state, the outer state, the
bytes absorbed and `U`. -/
def finArgs : List Instr :=
  scr .edx F.stWO ++ scr .esi F.st1O ++ [.mov .eax (argM 3), .alu .add .eax (.imm (BitVec.ofNat 32 (F.H.B + 4))),
    .mov .ecx (.imm 0)] ++ scr .edi F.uO

/-- `iterate`'s arguments: the key's states, `U`, `c - 1` and `T`. -/
def iterArgs : List Instr :=
  scr .esi F.st0O ++ scr .eax F.uO ++ [.mov .ecx (argM 4), .alu .sub .ecx (.imm 1)] ++ scr .edx F.tO

/-- The bytes of `T` the output still needs, `min (out_len - ebx, D)`, in `ecx`. -/
def outLen : Prog isa :=
  .seq (.block [.mov .ecx (argM 6), .alu .sub .ecx (.reg .ebx), .alu .cmp .ecx (.imm (BitVec.ofNat 32 F.H.D))])
    (.ite .b (.block []) (.block [.mov .ecx (.imm (BitVec.ofNat 32 F.H.D))]))

/-- The loop copying `esi` bytes of `T` to `edi`. -/
def outLoop : Prog isa :=
  .seq (.block [.mov .esi (.reg .ecx), .mov .edi (argM 5), .alu .add .edi (.reg .ebx), .mov .ecx (.imm 0)])
    (.loop (.block [.mov .eax (.reg .ebp), .alu .add .eax (.reg .ecx), .movzx8 .edx (at_ .eax F.tO),
      .mov .eax (.reg .edi), .alu .add .eax (.reg .ecx), .store8 (at_ .eax 0) .dl,
      .alu .add .ecx (.imm 1), .alu .cmp .ecx (.reg .esi)]) .ne)

/-- The bytes written, the next `INT (i)`, and whether the output is complete. -/
def advance : List Instr :=
  [.alu .add .ebx (.reg .esi), .mov .eax (.mem (at_ .ebp F.intO)), .bswap .eax, .alu .add .eax (.imm 1),
    .bswap .eax, .store (at_ .ebp F.intO) .eax, .mov .eax (argM 6), .alu .cmp .ebx (.reg .eax)]

/-- One block of the output. -/
def block : Prog isa :=
  .seq (copy .ebp F.stSO .ebp F.stWO F.H.S)
  (.seq (.block F.updArgs)
  (.seq (.frame (.push [.ebp, .ecx, .edx, .eax, .esi, .edi]) (.call F.H.updN F.H.updC) (.pop .eax 6))
  (.seq (.block F.finArgs)
  (.seq (.frame (.push [.ebp, .edi, .ecx, .eax, .esi, .edx]) (.call F.hfN F.hfC) (.pop .eax 6))
  (.seq (copy .ebp F.uO .ebp F.tO F.H.D)
  (.seq (.block F.iterArgs)
  (.seq (.frame (.push [.ebp, .edx, .ecx, .eax, .esi]) (.call F.itN F.itC) (.pop .eax 5))
  (.seq F.outLen
  (.seq F.outLoop
    (.block F.advance))))))))))

def pbkdf2 : Prog isa :=
  .seq (.block F.prologue)
  (.seq F.key
  (.seq F.setup
  (.seq (.block F.loopInit)
  (.seq (.ite .e (.block []) (.loop F.block .ne))
    (.block F.L.restore)))))

end Fns

end VG.Impl.Pbkdf2.Whole.X86
