import VerifiedGarbage.Impl.Hmac.Generic.AArch64

/-!
# PBKDF2-HMAC over any streaming hash function: AArch64 implementation

`iterate(key = x0, u = x1, n = w2, t = x3, scratch = x4)` runs `n` steps
`U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for the key
whose inner and outer streaming states are at `key` and `key + S`. Each step
copies the inner state into `scratch`, absorbs `U` into it with `update` and
finalizes it; then does the same with the outer state and that digest, which
gives the next `U`.

`scratch` is laid out as for HMAC (`VG.Impl.Hmac.Generic.AArch64`): the
working space of the functions we call, our caller's registers and our
return address, then the state (`S` bytes), the inner digest and `U` (`F`
bytes each). Registers: `x19` = `key`, `x20` = `t`, `x22` = the steps left,
`x23` = `scratch`, `x24` = the byte index.

`n` is a 32-bit argument, whose register's upper half is whatever the caller
left there (possibly secret): the first instruction zero-extends it.
-/

namespace VG.Impl.Pbkdf2.Generic.AArch64

open VG.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Impl.Hmac.Generic.AArch64 (Hash copy left)

variable (H : Hash)

/-- Where the state being hashed is in `scratch`. -/
def stO : Nat := H.buf

/-- Where the inner digest is. -/
def tmpO : Nat := H.buf + H.S

/-- Where `U` is. -/
def uO : Nat := H.buf + H.S + H.F

/-- `T ← T ⊕ U`, byte by byte. -/
def xorLoop : Prog isa :=
  .seq (.block [.movz .x .x24 0 0])
    (.loop (.block ([.add .x .x12 .x23 .x24, .ldrb .x9 .x12 (uO H), .add .x .x13 .x20 .x24,
      .ldrb .x10 .x13 0, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x13 0, .addImm .x .x24 .x24 1] ++
      left H.D)) (.nonzero .x .x11))

/-- `movz x1, B + D`: the count of a state that has absorbed a block and a digest. -/
def count2 : List Instr := [.movz .x .x1 (BitVec.ofNat 16 (H.B + H.D)) 0]

/-- `x0 ← scratch + stO`: the state being hashed. -/
def atSt : List Instr := [.addImm .x .x0 .x23 (stO H)]

/-- One step. -/
def body : Prog isa :=
  .seq (copy .x19 0 .x23 (stO H) H.S)
  (.seq (H.callUpd (atSt H) H.B (uO H) H.D)
  (.seq (H.callFin (atSt H) (count2 H) (tmpO H))
  (.seq (copy .x19 H.S .x23 (stO H) H.S)
  (.seq (H.callUpd (atSt H) H.B (tmpO H) H.D)
  (.seq (H.callFin (atSt H) (count2 H) (uO H))
  (.seq (xorLoop H)
    (.block [.subImm .x .x22 .x22 1])))))))

def prologue : List Instr :=
  H.save ++ [mov .x22 .x2, mov .x19 .x0, mov .x20 .x3, mov .x23 .x4]

/-- `iterate`, once `n` is zero-extended. -/
def main : Prog isa :=
  .seq (.block (prologue H))
  (.seq (copy .x1 0 .x23 (uO H) H.D)
  (.seq (.ite (.zero .x .x22) (.block []) (.loop (body H) (.nonzero .x .x22)))
    (.block H.restore)))

def iterate : Prog isa := .seq (.block [.addImm .w .x2 .x2 0]) (main H)

end VG.Impl.Pbkdf2.Generic.AArch64
