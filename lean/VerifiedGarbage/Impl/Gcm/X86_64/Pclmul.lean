import VerifiedGarbage.Spec.Gcm
import VerifiedGarbage.TCB.X86_64.Isa

/-!
# GHASH with PCLMULQDQ on x86-64

`vg_ghash_pclmul(h = rdi, y = rsi, data = rdx, n = rcx, scratch = r8)`, with
the contract of `vg_ghash` (`Spec.Gcm.ghashContract`), for CPUs with
PCLMULQDQ and SSSE3 (for `pshufb`).

A block is loaded and byte-reversed with `pshufb`, so that the register
holds the block's value as SP 800-38D reads it (the first byte the most
significant): bit `127 − i` of the register is the coefficient of `xⁱ` of
the field element. In this bit-reflected representation:

* the carry-less product (four `pclmulqdq`) of two registers `a`, `b` is
  `x · a · b`, as 256 bits `hi : lo` (`hi` holding the low powers), and the
  product `x¹²⁸ · lo` is reduced into 128 bits with two `pclmulqdq` by the
  constant `0xc2 · 2⁵⁶` (`x + x² + x⁷`, reflected) and two qword swaps, so
  that `mul(a, b) = hi ⊕ red(lo) = x · a · b` in GF(2¹²⁸);
* to cancel the factor `x`, the hash subkey is used as `H' = H · x⁻¹`,
  which is `H` shifted left by one bit, XORed with
  `0xc2000000000000000000000000000001` (`x⁻¹`) if the bit shifted out was 1
  (a mask, not a branch);
* `H'ᵏ⁺¹ = mul(H'ᵏ, H') = Hᵏ⁺¹ · x⁻¹` for `k = 1, 2, 3` are computed once
  per call and kept in `xmm3`–`xmm6`, and four blocks at a time
  `Y ← mul(Y ⊕ X₁, H'⁴) ⊕ mul(X₂, H'³) ⊕ mul(X₃, H'²) ⊕ mul(X₄, H')`,
  reducing the sum of the four products once; the remaining blocks go one
  at a time.

`pmuludq` is not used. `scratch` is not used, and no callee-saved register
is written. Every branch and every address depends only on the pointers and
`n`.
-/

namespace VG.Impl.Gcm.X86_64.Pclmul

open VG.X86_64

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The `pshufb` mask that reverses the 16 bytes. -/
def revMask : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128

/-- The reduction constant: `0xc2 · 2⁵⁶` in the upper quadword. -/
def poly : BitVec 128 := 0xc2000000000000000000000000000000#128

/-- `x⁻¹` in the reflected representation. -/
def xInv : BitVec 128 := 0xc2000000000000000000000000000001#128

/-- The 128-bit constant `c` into `x`, through `rax` and `xmm12`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .xop (.movq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .xop (.movq .xmm12 .rax),
   .xop (.bin .punpcklqdq x .xmm12)]

/-! Registers: `xmm0` the byte-reversal mask, `xmm1` the reduction constant,
`xmm2` `Y`, `xmm3`–`xmm6` `H'`–`H'⁴`, `xmm7` a block, `xmm8`–`xmm10` the
product (`lo`, `mid`, `hi`), `xmm11`–`xmm14` temporaries. -/

/-- Clear the product. -/
def zero : List Instr :=
  [.xop (.bin .pxor .xmm8 .xmm8), .xop (.bin .pxor .xmm9 .xmm9), .xop (.bin .pxor .xmm10 .xmm10)]

/-- Add the carry-less product of `a` and `b` to `lo`, `mid`, `hi`. -/
def acc (a b : XReg) : List Instr :=
  [.xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 b 0x00), .xop (.bin .pxor .xmm8 .xmm11),
   .xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 b 0x11), .xop (.bin .pxor .xmm10 .xmm11),
   .xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 b 0x01), .xop (.bin .pxor .xmm9 .xmm11),
   .xop (.bin .movdqa .xmm11 a), .xop (.pclmulqdq .xmm11 b 0x10), .xop (.bin .pxor .xmm9 .xmm11)]

/-- One step of the reduction of `lo`: `lo ← swap(lo) ⊕ clmul(lo₀, 0xc2 · 2⁵⁶)`. -/
def fold : List Instr :=
  [.xop (.bin .movdqa .xmm11 .xmm8), .xop (.pclmulqdq .xmm11 .xmm1 0x10),
   .xop (.pshufd .xmm8 .xmm8 0x4e), .xop (.bin .pxor .xmm8 .xmm11)]

/-- The product, reduced, into `d`. -/
def reduce (d : XReg) : List Instr :=
  [.xop (.bin .movdqa .xmm11 .xmm9), .xop (.shift .psrldq .xmm11 8), .xop (.bin .pxor .xmm10 .xmm11),
   .xop (.shift .pslldq .xmm9 8), .xop (.bin .pxor .xmm8 .xmm9)] ++ fold ++ fold ++
  [.xop (.bin .movdqa d .xmm10), .xop (.bin .pxor d .xmm8)]

/-- `d ← mul(a, b)`. -/
def mul (d a b : XReg) : List Instr := zero ++ acc a b ++ reduce d

/-- Block `j` of the data into `xmm7`, as a field element. -/
def load (j : Nat) : List Instr :=
  [.movdquLoad .xmm7 (at_ .rdx (16 * j)), .xop (.bin .pshufb .xmm7 .xmm0)]

/-- `H' = H · x⁻¹` into `xmm3`, from `H` in `xmm7`. -/
def hInv : List Instr :=
  const .xmm13 xInv ++
  [.movImm64 .rax 0xffffffffffffffff, .xop (.movq .xmm14 .rax), .xop (.bin .punpcklqdq .xmm14 .xmm14),
   .xop (.bin .movdqa .xmm3 .xmm7), .xop (.shift .psllq .xmm3 1),
   .xop (.bin .movdqa .xmm11 .xmm7), .xop (.shift .psrlq .xmm11 63), .xop (.shift .pslldq .xmm11 8),
   .xop (.bin .por .xmm3 .xmm11),
   .xop (.pshufd .xmm11 .xmm7 0xff), .xop (.shift .psrld .xmm11 31), .xop (.bin .paddd .xmm11 .xmm14),
   .xop (.bin .pandn .xmm11 .xmm13), .xop (.bin .pxor .xmm3 .xmm11)]

def prologue : List Instr :=
  const .xmm0 revMask ++ const .xmm1 poly ++
  [.movdquLoad .xmm7 (at_ .rdi 0), .xop (.bin .pshufb .xmm7 .xmm0)] ++ hInv ++
  mul .xmm4 .xmm3 .xmm3 ++ mul .xmm5 .xmm4 .xmm3 ++ mul .xmm6 .xmm5 .xmm3 ++
  [.movdquLoad .xmm2 (at_ .rsi 0), .xop (.bin .pshufb .xmm2 .xmm0), .alu .cmp .rcx (.imm 4)]

/-- Four blocks. -/
def body4 : List Instr :=
  zero ++ load 0 ++ [.xop (.bin .pxor .xmm7 .xmm2)] ++ acc .xmm7 .xmm6 ++
  load 1 ++ acc .xmm7 .xmm5 ++ load 2 ++ acc .xmm7 .xmm4 ++ load 3 ++ acc .xmm7 .xmm3 ++
  reduce .xmm2 ++ [.alu .add .rdx (.imm 64), .alu .sub .rcx (.imm 4), .alu .cmp .rcx (.imm 4)]

/-- One block. -/
def body1 : List Instr :=
  zero ++ load 0 ++ [.xop (.bin .pxor .xmm7 .xmm2)] ++ acc .xmm7 .xmm3 ++
  reduce .xmm2 ++ [.alu .add .rdx (.imm 16), .alu .sub .rcx (.imm 1)]

def epilogue : List Instr :=
  [.xop (.bin .pshufb .xmm2 .xmm0), .movdquStore (at_ .rsi 0) .xmm2]

def ghash : Prog isa :=
  .seq (.block prologue)
    (.seq (.ite .b (.block []) (.loop (.block body4) .ae))
      (.seq (.block [.alu .test .rcx (.reg .rcx)])
        (.seq (.ite .e (.block []) (.loop (.block body1) .ne)) (.block epilogue))))

end VG.Impl.Gcm.X86_64.Pclmul
