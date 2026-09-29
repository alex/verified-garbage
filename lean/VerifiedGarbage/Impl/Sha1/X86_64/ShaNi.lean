import VerifiedGarbage.Spec.Sha1
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# SHA-1 compression function: x86-64 implementation with the SHA extensions

`vg_sha1_compress_shani(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`,
with the contract of `vg_sha1_compress`, for CPUs with the SHA extensions
and SSSE3.

* The working variables `a, b, c, d` are kept as `ABCD` in `xmm0` (`A` in
  bits 127:96, as `sha1rnds4` reads them). `e` is not kept: `sha1rnds4` adds
  it to the first message word it is given, and four rounds later it is the
  old `A` rotated left by 30, which `sha1nexte` adds to the next message
  word. So `xmm1` holds the value of `xmm0` before the last four rounds, or,
  at the start of a block, `e` in bits 127:96 and zeros elsewhere.
* The message schedule is kept four words to a register, `W₄ᵢ … W₄ᵢ₊₃` in
  `xmm(3 + i mod 4)` (`W₄ᵢ` in bits 127:96), computed with `sha1msg1`, `pxor`
  and `sha1msg2`.
* `xmm7` holds the `pshufb` mask that reverses the bytes of a register, which
  makes the message words big-endian and puts the first in bits 127:96;
  `xmm8` and `xmm9` hold `xmm0` and `xmm1` at the start of the block, and
  `xmm2` is a temporary.
* The hash value is loaded and stored 16 bytes at a time: `e` is loaded with
  `b, c, d` from `state + 4`, and stored with them there before `a, b, c, d`
  are stored at `state`.
* `scratch` is not used, and no callee-saved register is written. `rdi, rsi,
  rdx` (the pointers and the block count) are public; no address and no
  branch depends on anything else.
-/

namespace VG.Impl.Sha1.X86_64.ShaNi

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The register holding `W₄ᵢ … W₄ᵢ₊₃`. -/
def msg (i : Nat) : XReg := [.xmm3, .xmm4, .xmm5, .xmm6].getD (i % 4) .xmm3

/-- The 128-bit constant `c` into `x`, through `rax` and `xmm2`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .xop (.movq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .xop (.movq .xmm2 .rax),
   .xop (.bin .punpcklqdq x .xmm2)]

/-- The `pshufb` mask that reverses the bytes of a register. -/
def bswapMask : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128

/-- `W₄ᵢ … W₄ᵢ₊₃` into `msg i`: loaded from the block for `i < 4`, otherwise
from the previous sixteen words (whose register `msg i` held the oldest four). -/
def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.movdquLoad (msg i) (at_ .rsi (16 * i)), .xop (.bin .pshufb (msg i) .xmm7)]
  else
    [.xop (.bin .sha1msg1 (msg i) (msg (i + 1))),
     .xop (.bin .pxor (msg i) (msg (i + 2))),
     .xop (.bin .sha1msg2 (msg i) (msg (i + 3)))]

/-- Rounds `4i … 4i+3`, with `W₄ᵢ … W₄ᵢ₊₃` in `msg i`: `e` is added to `W₄ᵢ`
(for `i = 0`, it is in `xmm1`; after that, `sha1nexte` computes it from the
`ABCD` of four rounds before), and `sha1rnds4` selects the function and
constant of rounds `4i … 4i+3`, which are in group `i / 5` of 20 rounds. -/
def rounds4 (i : Nat) : List Instr :=
  [.xop (.bin .movdqa .xmm2 .xmm0),
   .xop (.bin (if i = 0 then .paddd else .sha1nexte) .xmm1 (msg i)),
   .xop (.sha1rnds4 .xmm0 .xmm1 (BitVec.ofNat 8 (i / 5))),
   .xop (.bin .movdqa .xmm1 .xmm2)]

/-- Rounds `0 … 4n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds4 n))

/-- One block. -/
def body : Prog isa :=
  .seq (.block [.xop (.bin .movdqa .xmm8 .xmm0), .xop (.bin .movdqa .xmm9 .xmm1)])
    (.seq (rounds 20)
      (.block [.xop (.bin .paddd .xmm0 .xmm8), .xop (.bin .sha1nexte .xmm1 .xmm9),
        .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]))

/-- Load the hash value `H₀ … H₄` as `ABCD` into `xmm0` and `E` into bits
127:96 of `xmm1`. -/
def load : List Instr :=
  const .xmm7 bswapMask ++
  [.movdquLoad .xmm0 (at_ .rdi 0), .xop (.pshufd .xmm0 .xmm0 0x1b),
   .movdquLoad .xmm1 (at_ .rdi 4), .xop (.shift .psrldq .xmm1 12),
   .xop (.shift .pslldq .xmm1 12)]

/-- Store `ABCD` and `E` back as the hash value: `H₁ … H₄` at `state + 4`,
then `H₀ … H₃` at `state`. -/
def store : List Instr :=
  [.xop (.pshufd .xmm0 .xmm0 0x1b),
   .xop (.bin .movdqa .xmm2 .xmm0),
   .xop (.shift .psrldq .xmm2 4),
   .xop (.bin .por .xmm2 .xmm1),
   .movdquStore (at_ .rdi 4) .xmm2, .movdquStore (at_ .rdi 0) .xmm0]

def compress : Prog isa :=
  .seq (.block (load ++ [.alu .test .rdx (.reg .rdx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block store))

end VG.Impl.Sha1.X86_64.ShaNi
