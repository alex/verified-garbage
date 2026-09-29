import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Impl.Sha1.AArch64.Stream
import VerifiedGarbage.Impl.Md5.AArch64.Stream
import VerifiedGarbage.Impl.Sha512.AArch64.Stream

/-!
# HMAC over any streaming hash function: AArch64 implementation

The same design as on x86-64 (`VG.Impl.Hmac.Generic.X86_64`): one
implementation of `vg_hmac_<hash>_init` and `vg_hmac_<hash>_finalize` (see
`VG.Spec.Hmac.Instance`) for every hash function `H` with a streaming
implementation, made only of calls of `H`'s own `init`, `update` and
`finalize` (`Hash`), and of byte loops around them.

* `init(inner = x0, outer = x1, key = x2, key_len = x3, scratch = x4)`
  writes `K₀ ⊕ ipad` and `K₀ ⊕ opad` into `scratch`, then starts each state
  with `init` and absorbs its padded key with `update`.
* `finalize(inner = x0, outer = x1, count = x2, out = x3, scratch = x4)`
  finalizes the inner state into `scratch`, copies the outer state over the
  inner one, absorbs that digest into it with `update`, finalizes it into
  `scratch` again, and copies the MAC to `out`.

`scratch` starts with the working space of the functions we call (`8 W`
bytes); then come our caller's `x19`–`x24` and our return address `x30`
(`saved`), which each call replaces, then our buffers. So the functions use
no stack of their own, and have no frames. The functions we call preserve
`x19`–`x28`, so our variables live there; `x23` is always `scratch`.

The loops count down: AArch64 branches on a register being zero, so each
loop computes the bytes left into `x11`.
-/

namespace VG.Impl.Hmac.Generic.AArch64

open VG.AArch64
open VG.Impl.Sha256.AArch64.Stream (mov)

/-- A streaming hash function's AArch64 functions, as we call them: the block
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

/-- `x11 ← n - x24`: the bytes left of `n`. -/
def left (n : Nat) : List Instr := [.movz .x .x11 (BitVec.ofNat 16 n) 0, .sub .x .x11 .x11 .x24]

/-- `n > 0` bytes copied from `[src + so]` to `[dst + d]`, with `x24` the
index. -/
def copy (src : Reg) (so : Nat) (dst : Reg) (d n : Nat) : Prog isa :=
  .seq (.block [.movz .x .x24 0 0])
    (.loop (.block ([.add .x .x12 src .x24, .ldrb .x9 .x12 so, .add .x .x13 dst .x24,
      .strb .x9 .x13 d, .addImm .x .x24 .x24 1] ++ left n)) (.nonzero .x .x11))

namespace Hash

variable (H : Hash)

/-- Where our caller's registers and our return address are saved in
`scratch`: after the working space of the functions we call (`x23`, which
holds `scratch`, last). -/
def saved : List (Reg × Nat) :=
  [(.x19, 8 * H.W), (.x20, 8 * H.W + 8), (.x21, 8 * H.W + 16), (.x22, 8 * H.W + 24),
    (.x24, 8 * H.W + 32), (.x30, 8 * H.W + 40), (.x23, 8 * H.W + 48)]

/-- Where our buffers start in `scratch`. -/
def buf : Nat := 8 * H.W + 56

/-- Saving them, with `scratch` in `x4`. -/
def save : List Instr := H.saved.map fun (r, d) => .str .x r .x4 d

/-- Restoring them, with `scratch` in `x23` (restored last). -/
def restore : List Instr := H.saved.map fun (r, d) => .ldr .x r .x23 d

/-- A call of `init` on the state at `st`. -/
def callInit (st : Reg) : Prog isa :=
  .seq (.block [mov .x0 st]) (.call H.initN H.initC)

/-- A call of `update` on the state at `x0` (set by `st`), with the count
`count` and the `len` bytes at `scratch + o`. -/
def callUpd (st : List Instr) (count o len : Nat) : Prog isa :=
  .seq (.block (st ++ [.movz .x .x1 (BitVec.ofNat 16 count) 0, .addImm .x .x2 .x23 o,
      .movz .x .x3 (BitVec.ofNat 16 len) 0, mov .x4 .x23]))
    (.call H.updN H.updC)

/-- A call of `finalize` on the state at `x0` (set by `st`), with the count
`count` (set by `count`) and the digest to `scratch + o`. -/
def callFin (st count : List Instr) (o : Nat) : Prog isa :=
  .seq (.block (st ++ count ++ [.addImm .x .x2 .x23 o, mov .x3 .x23])) (.call H.finN H.finC)

/-! ## `init`

Registers: `x19` = `inner`, `x20` = `outer`, `x21` = `key`, `x22` =
`key_len`, `x23` = `scratch`, `x24` = the byte index, `x14` = `0x36`
(`ipad`), `x15` = `0x5c` (`opad`). `K₀ ⊕ ipad` is at `scratch + buf`, and
`K₀ ⊕ opad` right after it. -/

/-- The key bytes, XORed with `ipad` and `opad` into the two blocks. -/
def keyLoop : Prog isa :=
  .loop (.block [.add .x .x13 .x21 .x24, .ldrb .x9 .x13 0, .add .x .x12 .x23 .x24,
    .logic .eor .x .x10 .x9 .x14, .strb .x10 .x12 H.buf, .logic .eor .x .x10 .x9 .x15,
    .strb .x10 .x12 (H.buf + H.B), .addImm .x .x24 .x24 1, .sub .x .x11 .x22 .x24])
    (.nonzero .x .x11)

/-- The zero bytes after the key, XORed likewise. -/
def padLoop : Prog isa :=
  .loop (.block ([.add .x .x12 .x23 .x24, .strb .x14 .x12 H.buf, .strb .x15 .x12 (H.buf + H.B),
    .addImm .x .x24 .x24 1] ++ left H.B)) (.nonzero .x .x11)

def initPrologue : List Instr :=
  H.save ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4,
    .movz .x .x14 0x36 0, .movz .x .x15 0x5c 0, .movz .x .x24 0 0]

/-- `K₀ ⊕ ipad` and `K₀ ⊕ opad` into `scratch`: the part of `init` before its calls. -/
def initKeys : Prog isa :=
  .seq (.block H.initPrologue)
  (.seq (.ite (.zero .x .x22) (.block []) H.keyLoop)
  (.seq (.block (left H.B))
    (.ite (.zero .x .x11) (.block []) H.padLoop)))

def init : Prog isa :=
  .seq H.initKeys
  (.seq (H.callInit .x19)
  (.seq (H.callUpd [mov .x0 .x19] 0 H.buf H.B)
  (.seq (H.callInit .x20)
  (.seq (H.callUpd [mov .x0 .x20] 0 (H.buf + H.B) H.B)
    (.block H.restore)))))

/-! ## `finalize`

Registers: `x19` = `inner`, `x20` = `outer`, `x21` = `out`, `x23` =
`scratch`, `x24` = the byte index. The digests are written to
`scratch + buf`. -/

def finPrologue : List Instr :=
  H.save ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x3, mov .x23 .x4]

def finalize : Prog isa :=
  .seq (.block H.finPrologue)
  (.seq (H.callFin [] [mov .x1 .x2] H.buf)
  (.seq (copy .x20 0 .x19 0 H.S)
  (.seq (H.callUpd [mov .x0 .x19] H.B H.buf H.D)
  (.seq (H.callFin [mov .x0 .x19] [.movz .x .x1 (BitVec.ofNat 16 (H.B + H.D)) 0] H.buf)
  (.seq (copy .x23 H.buf .x21 0 H.D)
    (.block H.restore))))))

end Hash

end VG.Impl.Hmac.Generic.AArch64
