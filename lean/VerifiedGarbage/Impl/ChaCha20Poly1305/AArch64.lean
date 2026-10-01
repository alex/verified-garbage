import VerifiedGarbage.Impl.ChaCha20.AArch64.XorCallee
import VerifiedGarbage.Impl.Poly1305.AArch64

/-!
# ChaCha20-Poly1305: AArch64 implementation

`vg_chacha20_poly1305_seal(ctx = x0, aad = x1, aad_len = x2, data = x3, len = x4)`
and `vg_chacha20_poly1305_open` (the same arguments, returning `w0`), composed
of calls of the verified ChaCha20 and Poly1305 functions.

The context (1024 bytes, see `VG.Spec.ChaCha20Poly1305.sealContract`):

* `[0, 32)`: the key; `[32, 44)`: the nonce; `[48, 64)`: the tag;
* `[64, 128)`: the ChaCha20 state;
* `[128, 448)`: the working space of `vg_chacha20_xor` (the first 32 bytes of
  the block with counter 0 are the one-time Poly1305 key);
* `[448, 576)`: the Poly1305 state;
* `[576, 592)`: the padded last block of the additional data or the data;
* `[592, 640)`: our caller's `x21`–`x25` and our return address `x30`;
* `[640, 656)`: the tag computed by `open`;
* `[656, 672)`: the lengths block;
* `[672, 800)`: the working space of `vg_poly1305_finalize` (`scratch`).

`x21` holds the context, `x22` the data, `x23` its length, `x24` the
additional data and `x25` its length throughout: they are callee-saved, and
no callee writes them (`vg_chacha20_xor` saves and restores `x19` and `x20`,
which we therefore do not use), so they stay public for the constant-time
analysis. A call (`bl`) stores nothing in memory, so no stack is used.

The model has no register-offset addressing and no flags: a padded last
block is copied a byte at a time through advancing pointers, counting down to
zero with `cbnz`, and the tags are compared without a branch, as
`1 - ((x | -x) >> 63)` of the OR of their XORs `x`.

Only the pointers and the lengths can affect timing: the branches are on the
lengths, and every address is a pointer plus a constant or a count.
-/

namespace VG.Impl.ChaCha20Poly1305.AArch64

open VG.AArch64
open VG.Impl.ChaCha20.AArch64 (XorCallee)
open VG.Impl.ChaCha20.AArch64.Xor (mov)

/-- The registers saved in the context, and where. -/
def saved : List (Reg × Nat) := [(.x22, 600), (.x23, 608), (.x24, 616), (.x25, 624), (.x30, 632),
  (.x21, 592)]

/-- Save them, with the context in `x0`. -/
def save : List Instr := saved.map fun (r, d) => .str .x r .x0 d
/-- Restore them (`x21`, the base, last). -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x21 d

/-- The arguments moved to where they are kept. -/
def moves : List Instr := [mov .x21 .x0, mov .x24 .x1, mov .x25 .x2, mov .x22 .x3, mov .x23 .x4]

/-- The ChaCha20 constants. -/
def consts : List (BitVec 32) := [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- Word `k` of the ChaCha20 state for counter 0 into `w9`: a constant (0–3),
the key (4–11), the counter (12) or the nonce (13–15). -/
def stSrc (k : Nat) : List Instr :=
  if k < 4 then
    let c := consts.getD k 0
    [.movz .w .x9 (c.extractLsb' 0 16) 0, .movk .w .x9 (c.extractLsb' 16 16) 1]
  else if k < 12 then [.ldr .w .x9 .x21 (4 * (k - 4))]
  else if k = 12 then [.movz .w .x9 0 0]
  else [.ldr .w .x9 .x21 (32 + 4 * (k - 13))]

/-- Word `k` of the ChaCha20 state, at `x21 + 64 + 4k`. -/
def stW (k : Nat) : List Instr := stSrc k ++ [.str .w .x9 .x21 (64 + 4 * k)]

/-- The ChaCha20 state for counter 0. -/
def initState : List Instr := (List.range 16).flatMap stW

/-- Saves the registers, moves the arguments, and computes the one-time key
and the Poly1305 state for it. -/
def prologue : Prog isa :=
  .seq (.block (save ++ moves ++ initState ++ [.addImm .x .x0 .x21 64, .addImm .x .x1 .x21 128]))
  (.seq (.call "vg_chacha20_block" VG.Impl.ChaCha20.AArch64.block)
  (.seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 128])
    (.call "vg_poly1305_init" Impl.Poly1305.AArch64.init)))

/-- Copies the `x10` (nonzero) bytes at `x1` to `x9`, advancing both. -/
def copyLoop : Prog isa :=
  .loop (.block [.ldrb .x11 .x1 0, .strb .x11 .x9 0, .addImm .x .x1 .x1 1, .addImm .x .x9 .x9 1,
    .subImm .x .x10 .x10 1]) (.nonzero .x .x10)

/-- The last `x10` bytes (1 to 15), at `x1`, padded with zeros, absorbed. -/
def padTail : Prog isa :=
  .seq (.block [.movz .x .x11 0 0, .str .x .x11 .x21 576, .str .x .x11 .x21 584,
    .addImm .x .x9 .x21 576])
  (.seq copyLoop
  (.seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 576, .movz .x .x2 1 0])
    (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.blocks)))

/-- The `n` bytes at `p`, padded with zeros to a multiple of 16, absorbed. -/
def macPad (p n : Reg) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, mov .x1 p, .lsr .x .x2 n 4])
  (.seq (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.blocks)
  (.seq (.block [.lsl .x .x10 n 60, .lsr .x .x10 .x10 60])
    (.ite (.zero .x .x10) (.block [])
      (.seq (.block [.sub .x .x9 n .x10, .add .x .x1 p .x9]) padTail))))

/-- The ChaCha20 counter set to 1, and the data encrypted or decrypted. -/
def cryptWith (c : XorCallee) : Prog isa :=
  .seq (.block [.movz .w .x9 1 0, .str .w .x9 .x21 112, .addImm .x .x0 .x21 64, mov .x1 .x22,
    mov .x2 .x23, .addImm .x .x3 .x21 128])
    (.call c.name c.code)

/-- The lengths block. -/
def lengths : List Instr := [.str .x .x25 .x21 656, .str .x .x23 .x21 664]

/-- The lengths block absorbed. -/
def absorbLengths : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, .addImm .x .x1 .x21 656, .movz .x .x2 1 0])
    (.call "vg_poly1305_blocks" Impl.Poly1305.AArch64.blocks)

/-- The tag written to `x21 + out`: the message is whole blocks, so its
length (`count`) is 0 modulo 16, and nothing is buffered. -/
def finalizeTo (out : Nat) : Prog isa :=
  .seq (.block [.addImm .x .x0 .x21 448, .movz .x .x1 0 0, .addImm .x .x2 .x21 out,
    .addImm .x .x3 .x21 672])
    (.call "vg_poly1305_finalize" Impl.Poly1305.AArch64.finalize)

def sealWith (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (.block lengths)
  (.seq (cryptWith c)
  (.seq (macPad .x22 .x23)
  (.seq absorbLengths
  (.seq (finalizeTo 48)
    (.block restore)))))))

/-- `x0 = 1` if the computed tag (at `x21 + 640`) is the received one (at
`x21 + 48`), else 0, without a branch: with `x` the OR of the XORs of their
words, `(x | -x) >> 63` is 0 if `x = 0` and 1 otherwise. -/
def compare : List Instr :=
  [.ldr .x .x9 .x21 640, .ldr .x .x10 .x21 48, .logic .eor .x .x9 .x9 .x10,
   .ldr .x .x10 .x21 648, .ldr .x .x11 .x21 56, .logic .eor .x .x10 .x10 .x11,
   .logic .orr .x .x9 .x9 .x10,
   .movz .x .x10 0 0, .sub .x .x10 .x10 .x9, .logic .orr .x .x9 .x9 .x10, .lsr .x .x9 .x9 63,
   .movz .x .x10 1 0, .sub .x .x0 .x10 .x9]

def openWith (c : XorCallee) : Prog isa :=
  .seq prologue
  (.seq (macPad .x24 .x25)
  (.seq (macPad .x22 .x23)
  (.seq (.block lengths)
  (.seq absorbLengths
  (.seq (cryptWith c)
  (.seq (finalizeTo 640)
    (.block (compare ++ restore))))))))

def crypt := cryptWith .scalar
def «seal» := sealWith .scalar
def «open» := openWith .scalar

end VG.Impl.ChaCha20Poly1305.AArch64
