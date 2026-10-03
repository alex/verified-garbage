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
cleared.

With sixteen blocks or more, each pair is multiplied, lane by lane, by `H'⁸`
in both lanes of `ymm7`, giving `H'⁹`–`H'¹⁶` in `ymm6` (`H'¹⁰`, `H'⁹`) to
`ymm3` (`H'¹⁶`, `H'¹⁵`). Sixteen blocks at a time, as eight 256-bit loads
(block `2k + l` in lane `l` of the `k`-th), `Y` is XORed into block 0 and

  `Y ← Σₖ mul(X₂ₖ, H'¹⁶⁻²ᵏ) ⊕ mul(X₂ₖ₊₁, H'¹⁵⁻²ᵏ)`,

each lane accumulating its eight products with the VEX.256 forms of
`vg_ghash_pclmul`'s instructions, which act on each lane as those do on an
SSE register; each lane's sum is reduced the same way (the reduction is
linear, so the two lanes' results add up to the reduction of the sum), and
the two are added into `xmm2`. The product with `Y` is accumulated last, so
that the next blocks' products do not wait for the reduction of the last
ones. After this loop, `H'`–`H'⁴` are copied back to `xmm3`–`xmm6` from
`ymm12` and `ymm13`, and eight blocks or more left go through a loop doing
the same with eight blocks and `ymm12`–`ymm15`.

After the loops, `vzeroupper` clears the upper lanes (so that the SSE code
that follows pays no transition penalty), and the blocks left (fewer than
eight) go through `vg_ghash_pclmul`'s loops and epilogue
(`Pclmul.ghashTail`), with `xmm0`–`xmm6` as it left them.

`pmuludq` is not used. `scratch` is not used, and no callee-saved register
is written. Every branch and every address depends only on the pointers and
`n`.
-/

namespace VG.Impl.Gcm.X86_64.Vpclmul

open VG.X86_64
open VG.Impl.Gcm.X86_64.Pclmul (at_ mul prologue ghashTail)

/-! Registers: `ymm0` the byte-reversal mask, `ymm1` the reduction constant,
`xmm2` `Y`, `ymm7` two blocks, `ymm8`–`ymm10` the products (`lo`, `mid`,
`hi`) of each lane, `ymm11` a temporary, `ymm12`–`ymm15` the powers `H'`–`H'⁸`
and, in the sixteen-block loop, `ymm3`–`ymm6` the powers `H'⁹`–`H'¹⁶`. -/

/-- The power register of the `k`-th 256-bit load of an eight-block body. -/
def preg : Nat → XReg
  | 0 => .xmm15 | 1 => .xmm14 | 2 => .xmm13 | _ => .xmm12

/-- The power register of the `k`-th 256-bit load of a sixteen-block body. -/
def preg16 : Nat → XReg
  | 0 => .xmm3 | 1 => .xmm4 | 2 => .xmm5 | 3 => .xmm6 | 4 => .xmm15 | 5 => .xmm14 | 6 => .xmm13
  | _ => .xmm12

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
(with `Y` added to block 0), and their products with the powers in `p`. -/
def ld (k : Nat) (p : XReg) : List Instr :=
  [.vmovdquLoad .l256 .xmm7 (at_ .rdx (32 * k)), .vop (.vbin .vpshufb .l256 .xmm7 .xmm7 .xmm0)] ++
  (if k = 0 then [.vop (.vbin .vpxor .l256 .xmm7 .xmm7 .xmm2)] else []) ++ acc .xmm7 p

/-- The `k`-th load of an eight-block body. -/
def load (k : Nat) : List Instr := ld k (preg k)

/-- The `k`-th load of a sixteen-block body. -/
def load16 (k : Nat) : List Instr := ld k (preg16 k)

/-- The two lanes' blocks added into `xmm2` (`VEX.128`, so its upper lane is
cleared). -/
def combine : List Instr :=
  [.vop (.vextracti128 .xmm11 .xmm7 1), .vop (.vbin .vpxor .l128 .xmm2 .xmm7 .xmm11)]

def next : List Instr := [.alu .add .rdx (.imm 128), .alu .sub .rcx (.imm 8), .alu .cmp .rcx (.imm 8)]

/-- Eight blocks. -/
def body8 : List Instr :=
  zero ++ load 0 ++ load 1 ++ load 2 ++ load 3 ++ reduce .xmm7 ++ combine ++ next

/-- `d ← mul(p, H'⁸)` in each lane, with `H'⁸` in both lanes of `ymm7`. -/
def mulPair (d p : XReg) : List Instr := zero ++ acc p .xmm7 ++ reduce d

/-- `H'⁹`–`H'¹⁶`, paired in the lanes of `ymm3`–`ymm6`. -/
def powers16 : List Instr :=
  [.vop (.vinserti128 .xmm7 .xmm15 .xmm15 1)] ++ mulPair .xmm3 .xmm15 ++ mulPair .xmm4 .xmm14 ++
  mulPair .xmm5 .xmm13 ++ mulPair .xmm6 .xmm12

def next16 : List Instr :=
  [.alu .add .rdx (.imm 256), .alu .sub .rcx (.imm 16), .alu .cmp .rcx (.imm 16)]

/-- Sixteen blocks, the product with `Y` last. -/
def body16 : List Instr :=
  zero ++ load16 1 ++ load16 2 ++ load16 3 ++ load16 4 ++ load16 5 ++ load16 6 ++ load16 7 ++ load16 0 ++
  reduce .xmm7 ++ combine ++ next16

/-- `H'`–`H'⁴` back into `xmm3`–`xmm6`, from `ymm12` and `ymm13`. -/
def restore : List Instr :=
  [.vop (.vextracti128 .xmm3 .xmm12 1), .vop (.vmovdqa .l128 .xmm4 .xmm12),
   .vop (.vextracti128 .xmm5 .xmm13 1), .vop (.vmovdqa .l128 .xmm6 .xmm13)]

/-- With eight blocks or more (after `cmp rcx, 8`): the powers, sixteen blocks
at a time, then eight. -/
def wide : Prog isa :=
  .seq (.block (powers ++ [.alu .cmp .rcx (.imm 16)]))
    (.seq (.ite .b (.block []) (.seq (.block powers16) (.seq (.loop (.block body16) .ae) (.block restore))))
      (.seq (.block [.alu .cmp .rcx (.imm 8)]) (.ite .b (.block []) (.loop (.block body8) .ae))))

def ghash : Prog isa :=
  .seq (.block (prologue ++ [.alu .cmp .rcx (.imm 8)]))
    (.seq (.ite .b (.block []) wide)
      (.seq (.block [.vop .vzeroupper, .alu .cmp .rcx (.imm 4)]) ghashTail))

end VG.Impl.Gcm.X86_64.Vpclmul
