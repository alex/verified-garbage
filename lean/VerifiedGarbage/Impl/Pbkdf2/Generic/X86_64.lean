import VerifiedGarbage.Impl.Hmac.Generic.X86_64

/-!
# PBKDF2-HMAC over any streaming hash function: x86-64 implementation

`iterate(key = rdi, u = rsi, n = edx, t = rcx, scratch = r8)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + S`. Each
step copies the inner state into `scratch`, absorbs `U` into it with
`update` and finalizes it; then does the same with the outer state and that
digest, which gives the next `U`.

`scratch` is laid out as for HMAC (`VG.Impl.Hmac.Generic.X86_64`): the
working space of the functions we call, our caller's registers, then the
state (`S` bytes), the inner digest and `U` (`F` bytes each). Registers:
`rbx` = `key`, `r12` = `t`, `r13` = the steps left, `r15` = `scratch`,
`r14` = the byte index.
-/

namespace VG.Impl.Pbkdf2.Generic.X86_64

open VG.X86_64
open VG.Impl.Sha256.X86_64 (at_)
open VG.Impl.Hmac.Generic.X86_64 (Hash copy scr byteAt)

variable (H : Hash)

/-- Where the state being hashed is in `scratch`. -/
def stO : Nat := H.buf

/-- Where the inner digest is. -/
def tmpO : Nat := H.buf + H.S

/-- Where `U` is. -/
def uO : Nat := H.buf + H.S + H.F

/-- `T ← T ⊕ U`, byte by byte. -/
def xorLoop : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 0)])
    (.loop (.block [.movzx8 .rax (byteAt .r15 (uO H)), .movzx8 .rcx (byteAt .r12 0),
      .alu32 .xor .rax (.reg .rcx), .store8 (byteAt .r12 0) .rax, .alu .add .r14 (.imm 1),
      .alu .cmp .r14 (.imm (BitVec.ofNat 32 H.D))]) .ne)

/-- `mov32 rsi, B + D`: the count of a state that has absorbed a block and a digest. -/
def count2 : List Instr := [.mov32 .rsi (.imm (BitVec.ofNat 32 (H.B + H.D)))]

/-- One step. -/
def body : Prog isa :=
  .seq (copy .rbx 0 .r15 (stO H) H.S)
  (.seq (H.callUpd (scr .rdi (stO H)) H.B (uO H) H.D)
  (.seq (H.callFin (scr .rdi (stO H)) (count2 H) (tmpO H))
  (.seq (copy .rbx H.S .r15 (stO H) H.S)
  (.seq (H.callUpd (scr .rdi (stO H)) H.B (tmpO H) H.D)
  (.seq (H.callFin (scr .rdi (stO H)) (count2 H) (uO H))
  (.seq (xorLoop H)
    (.block [.alu .sub .r13 (.imm 1)])))))))

def prologue : List Instr :=
  H.save ++ [.mov32 .r13 (.reg .rdx), .mov .rbx (.reg .rdi), .mov .r12 (.reg .rcx),
    .mov .r15 (.reg .r8)]

def iterate : Prog isa :=
  .seq (.block (prologue H))
  (.seq (copy .rsi 0 .r15 (uO H) H.D)
  (.seq (.block [.alu .test .r13 (.reg .r13)])
  (.seq (.ite .e (.block []) (.loop (body H) .ne))
    (.block H.restore))))

end VG.Impl.Pbkdf2.Generic.X86_64
