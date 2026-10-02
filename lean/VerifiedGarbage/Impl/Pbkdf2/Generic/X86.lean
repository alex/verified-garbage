import VerifiedGarbage.Impl.Hmac.Generic.X86

/-!
# PBKDF2-HMAC over any streaming hash function: x86 (32-bit) implementation

`iterate(key, u, n, t, scratch)`, every argument on the stack (cdecl), runs
`n` steps `U ← HMAC (K₀, U)`, `T ← T ⊕ U` (`VG.Spec.Pbkdf2.iterate`), for
the key whose inner and outer streaming states are at `key` and `key + S`.
Each step copies the inner state into `scratch`, absorbs `U` into it with
`update` and finalizes it; then does the same with the outer state and that
digest, which gives the next `U`.

`scratch` is laid out as for HMAC (`VG.Impl.Hmac.Generic.X86`): the working
space of the functions we call, our caller's registers, then the state (`S`
bytes), the inner digest and `U` (`F` bytes each). Registers: `ebp` =
`scratch`, `edi` = the steps left; `key` and `t` are read from the stack
into `esi` when needed, which leaves `ebx` for the address of the state
being hashed and `esi` for the low word of `update`'s count.
-/

namespace VG.Impl.Pbkdf2.Generic.X86

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash copy scr at_)

variable (H : Hash)

/-- Where the state being hashed is in `scratch`. -/
def stO : Nat := H.buf

/-- Where the inner digest is. -/
def tmpO : Nat := H.buf + H.S

/-- Where `U` is. -/
def uO : Nat := H.buf + H.S + H.F

/-- `T ← T ⊕ U`, byte by byte, with `T` at `esi`. -/
def xorLoop : Prog isa :=
  .seq (.block [.mov .ecx (.imm 0)])
    (.loop (.block [.mov .eax (.reg .ebp), .alu .add .eax (.reg .ecx), .movzx8 .edx (at_ .eax (uO H)),
      .mov .eax (.reg .esi), .alu .add .eax (.reg .ecx), .movzx8 .ebx (at_ .eax 0), .alu .xor .edx (.reg .ebx),
      .store8 (at_ .eax 0) .dl, .alu .add .ecx (.imm 1), .alu .cmp .ecx (.imm (BitVec.ofNat 32 H.D))]) .ne)

/-- `ebx ← scratch + stO`: the state being hashed. -/
def atSt : List Instr := scr .ebx (stO H)

/-- `key`, from the stack. -/
def ldKey : List Instr := [.mov .esi (.mem (at_ .esp 4))]

/-- `t`, from the stack. -/
def ldT : List Instr := [.mov .esi (.mem (at_ .esp 16))]

/-- One step. -/
def body : Prog isa :=
  .seq (.block ldKey)
  (.seq (copy .esi 0 .ebp (stO H) H.S)
  (.seq (H.callUpd (atSt H) .ebx .esi H.B (uO H) H.D)
  (.seq (H.callFin (atSt H) H.count2 .ebx (tmpO H))
  (.seq (.block ldKey)
  (.seq (copy .esi H.S .ebp (stO H) H.S)
  (.seq (H.callUpd (atSt H) .ebx .esi H.B (tmpO H) H.D)
  (.seq (H.callFin (atSt H) H.count2 .ebx (uO H))
  (.seq (.block ldT)
  (.seq (xorLoop H)
    (.block [.alu .sub .edi (.imm 1)]))))))))))

def prologue : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ H.save ++ [.mov .ebp (.reg .eax), .mov .edi (.mem (at_ .esp 12)),
    .mov .esi (.mem (at_ .esp 8))]

def iterate : Prog isa :=
  .seq (.block (prologue H))
  (.seq (copy .esi 0 .ebp (uO H) H.D)
  (.seq (.block [.alu .test .edi (.reg .edi)])
  (.seq (.ite .e (.block []) (.loop (body H) .ne))
    (.block H.restore))))

end VG.Impl.Pbkdf2.Generic.X86
