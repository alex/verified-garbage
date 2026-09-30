import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# SHA-512 compression function: x86-64 implementation with the SHA512 extension

`vg_sha512_compress_shani(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`,
with the contract of `vg_sha512_compress`, for CPUs with the SHA512 extension
(`vsha512rnds2`, `vsha512msg1`, `vsha512msg2`) and AVX2.

* The working variables are kept as `ABEF` in `ymm1` and `CDGH` in `ymm2`
  (`A` in bits 255:192, as `vsha512rnds2` reads them), converted from and to
  the hash value's `[u64; 8]` layout once per call. Each `vsha512rnds2` does
  two rounds and swaps the roles of the two registers.
* Four rounds at a time, `Wₜ + Kₜ` for them is formed in `ymm0`: the four
  constants are loaded as immediates through `rax`, `xmm11` and `xmm12`,
  since the model has no constant pool; the second `vsha512rnds2` reads the
  upper two from `xmm0` after `vextracti128`.
* The message schedule is kept four words to a register, `W₄ᵢ … W₄ᵢ₊₃` in
  `ymm(3 + i mod 4)`, computed with `vsha512msg1`, `vperm2i128` and
  `vpalignr` (for `Wₜ₋₇`), `vpaddq` and `vsha512msg2`.
* `ymm8` holds the `vpshufb` mask that makes the message words big-endian;
  `ymm9` and `ymm10` hold the working variables at the start of the block.
* `scratch` is not used, and no callee-saved register is written;
  `vzeroupper` before returning avoids the penalty of dirty upper halves in
  the caller's SSE code. `rdi, rsi, rdx` (the pointers and the block count)
  are public; no address and no branch depends on anything else.
-/

namespace VG.Impl.Sha512.X86_64.ShaNi

open VG.X86_64
open VG.Spec.Sha512 (K)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The register holding `W₄ᵢ … W₄ᵢ₊₃`. -/
def msg (i : Nat) : XReg := [.xmm3, .xmm4, .xmm5, .xmm6].getD (i % 4) .xmm3

def vb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- The 64-bit constants `c₀`, `c₁` into the low and high quadwords of `x`
(its upper lane zeroed), through `rax` and `xmm11`. -/
def const2 (x : XReg) (c₀ c₁ : BitVec 64) : List Instr :=
  [.movImm64 .rax c₀, .vop (.vmovq x .rax), .movImm64 .rax c₁, .vop (.vmovq .xmm11 .rax),
   .vop (.vbin .vpunpcklqdq .l128 x x .xmm11)]

/-- `Kᵢ … Kᵢ₊₃` into `ymm0`, `Kᵢ` in bits 63:0, through `xmm12`. -/
def kQuad (i : Nat) : List Instr :=
  const2 .xmm0 (K i) (K (i + 1)) ++ const2 .xmm12 (K (i + 2)) (K (i + 3)) ++
  [.vop (.vinserti128 .xmm0 .xmm0 .xmm12 1)]

/-- The `vpshufb` mask that reverses the bytes of each quadword. -/
def bswapMask : BitVec 128 := 0x08090a0b0c0d0e0f0001020304050607#128

/-- `W₄ᵢ … W₄ᵢ₊₃` into `msg i`: loaded from the block for `i < 4`, otherwise
from the previous sixteen words (whose register `msg i` held the oldest four). -/
def schedule (i : Nat) : List Instr :=
  if i < 4 then
    [.vmovdquLoad .l256 (msg i) (at_ .rsi (32 * i)), vb .vpshufb (msg i) (msg i) .xmm8]
  else
    [.vop (.vsha512msg1 (msg i) (msg (i + 1))),
     .vop (.vperm2i128 .xmm7 (msg (i + 2)) (msg (i + 3)) 0x21),
     .vop (.vpalignr .l256 .xmm7 .xmm7 (msg (i + 2)) 8),
     vb .vpaddq (msg i) (msg i) .xmm7,
     .vop (.vsha512msg2 (msg i) (msg (i + 3)))]

/-- Rounds `4i … 4i+3`, with `W₄ᵢ … W₄ᵢ₊₃` in `msg i`. -/
def rounds4 (i : Nat) : List Instr :=
  kQuad (4 * i) ++
  [vb .vpaddq .xmm0 .xmm0 (msg i),
   .vop (.vsha512rnds2 .xmm2 .xmm1 .xmm0),
   .vop (.vextracti128 .xmm0 .xmm0 1),
   .vop (.vsha512rnds2 .xmm1 .xmm2 .xmm0)]

/-- Rounds `0 … 4n-1`. -/
def rounds : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (rounds n) (.block (schedule n ++ rounds4 n))

/-- One block. -/
def body : Prog isa :=
  .seq (.block [.vop (.vmovdqa .l256 .xmm9 .xmm1), .vop (.vmovdqa .l256 .xmm10 .xmm2)])
    (.seq (rounds 20)
      (.block [vb .vpaddq .xmm1 .xmm1 .xmm9, vb .vpaddq .xmm2 .xmm2 .xmm10,
        .alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 1)]))

/-- The mask into both lanes of `ymm8`. -/
def mask : List Instr :=
  const2 .xmm8 (bswapMask.extractLsb' 0 64) (bswapMask.extractLsb' 64 64) ++
  [.vop (.vinserti128 .xmm8 .xmm8 .xmm8 1)]

/-- Load the hash value `H₀ … H₇` as `ABEF` (`H₀, H₁, H₄, H₅` from quadword 3
down) into `ymm1` and `CDGH` (`H₂, H₃, H₆, H₇`) into `ymm2`. -/
def load : List Instr :=
  mask ++
  [.vmovdquLoad .l256 .xmm1 (at_ .rdi 0), .vmovdquLoad .l256 .xmm2 (at_ .rdi 32),
   -- ymm7 := H₄ H₅ H₀ H₁ (from quadword 0), ymm2 := H₆ H₇ H₂ H₃
   .vop (.vperm2i128 .xmm7 .xmm2 .xmm1 0x20),
   .vop (.vperm2i128 .xmm2 .xmm2 .xmm1 0x31),
   -- each lane's two quadwords swapped: ABEF = H₅ H₄ H₁ H₀, CDGH = H₇ H₆ H₃ H₂
   .vop (.vpermq .xmm1 .xmm7 0xb1),
   .vop (.vpermq .xmm2 .xmm2 0xb1)]

/-- Store `ABEF` and `CDGH` back as the hash value, and clear the upper
halves. -/
def store : List Instr :=
  [.vop (.vpermq .xmm1 .xmm1 0xb1), .vop (.vpermq .xmm2 .xmm2 0xb1),
   -- ymm7 := H₀ H₁ H₂ H₃, ymm1 := H₄ H₅ H₆ H₇
   .vop (.vperm2i128 .xmm7 .xmm1 .xmm2 0x31),
   .vop (.vperm2i128 .xmm1 .xmm1 .xmm2 0x20),
   .vmovdquStore .l256 (at_ .rdi 0) .xmm7, .vmovdquStore .l256 (at_ .rdi 32) .xmm1,
   .vop .vzeroupper]

def compress : Prog isa :=
  .seq (.block (load ++ [.alu .test .rdx (.reg .rdx)]))
    (.seq (.ite .e (.block []) (.loop body .ne)) (.block store))

end VG.Impl.Sha512.X86_64.ShaNi
