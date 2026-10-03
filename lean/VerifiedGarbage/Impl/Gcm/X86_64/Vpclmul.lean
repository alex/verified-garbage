import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul

/-!
# GHASH with VPCLMULQDQ on x86-64

`vg_ghash_vpclmul(h = rdi, y = rsi, data = rdx, n = rcx, scratch = r8)`, with
the contract of `vg_ghash` (`Spec.Gcm.ghashContract`), for CPUs with
VPCLMULQDQ and AVX2 (and PCLMULQDQ and SSSE3, for the blocks left).

`vg_ghash_pclmul`'s prologue computes `H'`–`H'⁴` (`H'ᵏ = Hᵏ · x⁻¹`) into
`xmm3`–`xmm6` and loads `Y` into `xmm2`. With eight blocks or more, four
more products give `H'⁵`–`H'⁸`, and the eight powers are paired in the lanes
of `ymm15` (`H'⁸`, `H'⁷`), `ymm14` (`H'⁶`, `H'⁵`), `ymm13` (`H'⁴`, `H'³`) and
`ymm12` (`H'²`, `H'`); the byte-reversal mask and the reduction constant are
copied to the upper lanes of `ymm0` and `ymm1`, and the upper lane of `ymm2`
cleared. Eight blocks at a time, as four 256-bit loads (block `2k + l` in
lane `l` of the `k`-th), `Y` is XORed into block 0 and

  `Y ← Σₖ mul(X₂ₖ, H'⁸⁻²ᵏ) ⊕ mul(X₂ₖ₊₁, H'⁷⁻²ᵏ)`,

each lane accumulating its four products with the VEX.256 forms of
`vg_ghash_pclmul`'s instructions, which act on each lane as those do on an
SSE register; each lane's sum is reduced the same way (the reduction is
linear, so the two lanes' results add up to the reduction of the sum), and
the two are added into `xmm2`. After the loop, `vzeroupper` clears the upper
lanes (so that the SSE code that follows pays no transition penalty), and
the blocks left (fewer than eight) go through `vg_ghash_pclmul`'s loops and
epilogue (`Pclmul.ghashTail`), with `xmm0`–`xmm6` as it left them.

`pmuludq` is not used. `scratch` is not used, and no callee-saved register
is written. Every branch and every address depends only on the pointers and
`n`.
-/

namespace VG.Impl.Gcm.X86_64.Vpclmul

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ mul prologue ghashTail)

/-! Registers: `ymm0` the byte-reversal mask, `ymm1` the reduction constant,
`xmm2` `Y`, `ymm7` four blocks, `ymm8`–`ymm10` the products (`lo`, `mid`,
`hi`) of each lane, `ymm11` a temporary, `ymm12`–`ymm15` the powers. -/

/-- The power register of the `k`-th 256-bit load of a body. -/
def preg : Nat → XReg
  | 0 => .xmm15 | 1 => .xmm14 | 2 => .xmm13 | _ => .xmm12

/-- `H'⁵`–`H'⁸` from `H'` and `H'⁴`, and the lanes paired. -/
def powers : List Instr :=
  mul .xmm12 .xmm6 .xmm3 ++ mul .xmm13 .xmm12 .xmm3 ++ mul .xmm14 .xmm13 .xmm3 ++
  mul .xmm15 .xmm14 .xmm3 ++
  [.vop (.vinserti128 .xmm15 .xmm15 .xmm14 1), .vop (.vinserti128 .xmm14 .xmm13 .xmm12 1),
   .vop (.vinserti128 .xmm13 .xmm6 .xmm5 1), .vop (.vinserti128 .xmm12 .xmm4 .xmm3 1),
   .vop (.vinserti128 .xmm0 .xmm0 .xmm0 1), .vop (.vinserti128 .xmm1 .xmm1 .xmm1 1),
   .vop (.vmovdqa .l128 .xmm2 .xmm2)]

/-- Clear the products of both lanes. -/
def zero : List Instr :=
  [.vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm8), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm9),
   .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm10)]

/-- Add the carry-less products of the lanes of `a` and `b` to `lo`, `mid`,
`hi`. -/
def acc (a b : XReg) : List Instr :=
  [.vop (.vpclmulqdq .l256 .xmm11 a b 0x00), .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm11),
   .vop (.vpclmulqdq .l256 .xmm11 a b 0x11), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm11),
   .vop (.vpclmulqdq .l256 .xmm11 a b 0x01), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm11),
   .vop (.vpclmulqdq .l256 .xmm11 a b 0x10), .vop (.vbin .vpxor .l256 .xmm9 .xmm9 .xmm11)]

/-- One step of the reduction of `lo`, in each lane. -/
def fold : List Instr :=
  [.vop (.vpclmulqdq .l256 .xmm11 .xmm8 .xmm1 0x10), .vop (.vpshufd .l256 .xmm8 .xmm8 0x4e),
   .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm11)]

/-- Each lane's product, reduced, into that lane of `d`. -/
def reduce (d : XReg) : List Instr :=
  [.vop (.vshift .psrldq .l256 .xmm11 .xmm9 8), .vop (.vbin .vpxor .l256 .xmm10 .xmm10 .xmm11),
   .vop (.vshift .pslldq .l256 .xmm9 .xmm9 8), .vop (.vbin .vpxor .l256 .xmm8 .xmm8 .xmm9)] ++
  fold ++ fold ++ [.vop (.vbin .vpxor .l256 d .xmm10 .xmm8)]

/-- Blocks `2k` and `2k + 1` into the lanes of `ymm7`, as field elements
(with `Y` added to block 0), and their products with the powers. -/
def load (k : Nat) : List Instr :=
  [.vmovdquLoad .l256 .xmm7 (at_ .rdx (32 * k)), .vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)] ++
  (if k = 0 then [.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 (preg k)

/-- The two lanes' blocks added into `xmm2` (`VEX.128`, so its upper lane is
cleared). -/
def combine : List Instr :=
  [.vop (.vextracti128 .xmm11 .xmm7 1), .vop (.vbin .vpxor .l128 .xmm2 .xmm7 .xmm11)]

def next : List Instr := [.alu .add .rdx (.imm 128), .alu .sub .rcx (.imm 8), .alu .cmp .rcx (.imm 8)]

/-- Eight blocks. -/
def body8 : List Instr :=
  zero ++ load 0 ++ load 1 ++ load 2 ++ load 3 ++ reduce .xmm7 ++ combine ++ next

def ghash : Prog isa :=
  .seq (.block (prologue ++ [.alu .cmp .rcx (.imm 8)]))
    (.seq (.ite .b (.block []) (.seq (.block powers) (.loop (.block body8) .ae)))
      (.seq (.block [.vop .vzeroupper, .alu .cmp .rcx (.imm 4)]) ghashTail))

end VG.Impl.Gcm.X86_64.Vpclmul
