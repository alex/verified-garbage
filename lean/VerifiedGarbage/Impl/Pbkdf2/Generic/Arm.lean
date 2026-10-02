import VerifiedGarbage.Impl.Hmac.Generic.Arm

/-!
# PBKDF2-HMAC over any streaming hash function: 32-bit ARM implementation

`iterate(key = r0, u = r1, n = r2, t = r3, scratch = [sp])` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + S`: the same
design as on x86 (`VG.Impl.Pbkdf2.Generic.X86`). Each step
copies the inner state into `scratch`, absorbs `U` into it with `update` and
finalizes it; then does the same with the outer state and that digest, which
gives the next `U`.

`scratch` is laid out as for HMAC (`VG.Impl.Hmac.Generic.Arm`): the working
space of the functions we call, our caller's registers and our return
address, then the state (`S` bytes), the inner digest and `U` (`F` bytes
each). Registers: `r4` = `key`, `r5` = `t`, `r6` = the steps left, `r11` =
`scratch`, `r8` = the byte index, `r9` = the bytes left.
-/

namespace VG.Impl.Pbkdf2.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy scrAt)

variable (H : Hash)

/-- Where the state being hashed is in `scratch`. -/
def stO : Nat := H.buf

/-- Where the inner digest is. -/
def tmpO : Nat := H.buf + H.S

/-- Where `U` is. -/
def uO : Nat := H.buf + H.S + H.F

/-- `T ← T ⊕ U`, byte by byte. -/
def xorLoop : Prog isa :=
  .seq (.block [.mov .r8 (.imm 0), .movw .r9 (BitVec.ofNat 16 H.D)])
    (.loop (.block [.dp .add .r2 .r11 (.reg .r8), .ldrb .r12 .r2 (uO H), .dp .add .r2 .r5 (.reg .r8),
      .ldrb .r1 .r2 0, .dp .eor .r1 .r1 (.reg .r12), .strb .r1 .r2 0, .dp .add .r8 .r8 (.imm 1),
      .subs .r9 .r9 (.imm 1)]) .ne)

/-- `r2:r3 ← B + D`: the count of a state that has absorbed a block and a digest. -/
def count2 : List Instr := [.movw .r2 (BitVec.ofNat 16 (H.B + H.D)), .mov .r3 (.imm 0)]

/-- `r0 ← scratch + stO`: the state being hashed. -/
def atSt : List Instr := scrAt .r0 (stO H)

/-- One step. -/
def body : Prog isa :=
  .seq (copy .r4 0 .r11 (stO H) H.S)
  (.seq (H.callUpd (atSt H) H.B (uO H) H.D)
  (.seq (H.callFin (atSt H) (count2 H) (tmpO H))
  (.seq (copy .r4 H.S .r11 (stO H) H.S)
  (.seq (H.callUpd (atSt H) H.B (tmpO H) H.D)
  (.seq (H.callFin (atSt H) (count2 H) (uO H))
  (.seq (xorLoop H)
    (.block [.subs .r6 .r6 (.imm 1)])))))))

def prologue : List Instr :=
  [.ldrSp .r12 0] ++ H.save ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r3), .mov .r6 (.reg .r2),
    .mov .r11 (.reg .r12)]

def iterate : Prog isa :=
  .seq (.block (prologue H))
  (.seq (copy .r1 0 .r11 (uO H) H.D)
  (.seq (.block [.cmp .r6 (.imm 0)])
  (.seq (.ite .eq (.block []) (.loop (body H) .ne))
    (.block H.restore))))

end VG.Impl.Pbkdf2.Generic.Arm
