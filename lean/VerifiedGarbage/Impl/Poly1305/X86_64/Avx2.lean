import VerifiedGarbage.Impl.Poly1305.X86_64

/-!
# Poly1305 blocks: x86-64 implementation with AVX2

`vg_poly1305_blocks_avx2(state = rdi, blocks = rsi, n = rdx)`, with the
contract of `vg_poly1305_blocks`, for CPUs with AVX2.

Fewer than `minBlocks` blocks are left to `vg_poly1305_blocks`. Otherwise
the first `4 ⌊n / 4⌋` blocks are absorbed four at a time, as in OpenSSL's
`poly1305_blocks_avx2`, and the rest (fewer than four) by calling
`vg_poly1305_blocks`.

* Numbers modulo `p = 2¹³⁰ - 5` are kept in five 26-bit limbs
  (`x = x₀ + 2²⁶ x₁ + … + 2¹⁰⁴ x₄`), one per quadword, four numbers to a
  set of five `ymm` registers (quadword `k` of limb `i` in register `i`):
  the accumulators `H` (`ymm0`–`ymm4`) of four interleaved Horner
  evaluations. Block `4j + k` is added to lane `k` of `H`, and `H` is
  multiplied by `r⁴` after each four blocks, except after the last four,
  when lane `k` is multiplied by `r^(4 - k)`; the sum of the lanes is then
  `h` after all the blocks.
* A product `x · y` is `d_j = Σ_{i ≤ j} x_i y_{j - i} + 5 Σ_{i > j} x_i y_{5 + j - i}`
  (`2¹³⁰ ≡ 5`), with `vpmuludq` (`D`, `ymm5`–`ymm9`), then carried: each
  `d_j` keeps its low 26 bits and passes the rest up, `d₄`'s times 5 to
  `d₀`, which passes its carry to `d₁` once more. Every limb stays below
  `2²⁷` and every `d_j` below `2⁶⁰`, so no quadword overflows.
* Everything stays in registers: each quadword of the multipliers `Y`
  (`ymm11`–`ymm15`) holds a limb of `r⁴` in its low doubleword, which
  `vpmuludq` reads, and in its high doubleword the same limb of `r⁴`, `r³`,
  `r²` or `r` (lanes 0–3), which the last product shifts down. They are
  computed on entry by multiplying `r` (from the key) by itself. `ymm10` is
  scratch, and the mask `2²⁶ - 1` and the pad bit `2²⁴` are broadcast from
  `r8` and `r9` when needed.
* `vpmuludq` has MXCSR-configuration-dependent timing on some processors,
  so the code that uses it runs between Intel's prologue and epilogue
  (`stmxcsr`, `ldmxcsr` of `0x1FBF`, `lfence`, … `lfence`, `ldmxcsr` of the
  saved value; see "MCDT" in `TCB/X86_64/Isa.lean`), in the state's working
  space (bytes 120–127). Bits 31:16 of MXCSR are reserved and zero; the
  saved value is stored with them cleared, which `ldmxcsr` requires.
* At the end the lanes of `H` are summed, carried, reduced fully (`h + 5 - 2¹³⁰`
  if that is not negative), put back into three 64-bit words and stored,
  all in vector registers.

No callee-saved register is written, and `vzeroupper` precedes the call of
`vg_poly1305_blocks` and the return. The branches are on `n` only, and every
address is a pointer plus a constant, so only the pointers and `n` can
affect timing.
-/

namespace VG.Impl.Poly1305.X86_64.Avx2

open VG.X86_64
open VG.Impl.Poly1305.X86_64 (at_)

/-- Below this many blocks, the scalar code is faster. -/
def minBlocks : Nat := 16

/-- The accumulators, the products, the multipliers, and scratch. -/
def hreg : Nat → XReg
  | 0 => .xmm0 | 1 => .xmm1 | 2 => .xmm2 | 3 => .xmm3 | _ => .xmm4
def dreg : Nat → XReg
  | 0 => .xmm5 | 1 => .xmm6 | 2 => .xmm7 | 3 => .xmm8 | _ => .xmm9
def yreg : Nat → XReg
  | 0 => .xmm11 | 1 => .xmm12 | 2 => .xmm13 | 3 => .xmm14 | _ => .xmm15
def tP : XReg := .xmm10

def v (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)
def srl (d a : XReg) (n : BitVec 8) : Instr := .vop (.vshift .psrlq .l256 d a n)
def sll (d a : XReg) (n : BitVec 8) : Instr := .vop (.vshift .psllq .l256 d a n)

/-- `r` into every quadword of `d`. -/
def bcast (d : XReg) (r : Reg) : List Instr := [.vop (.vmovq d r), .vop (.vpbroadcastq .l256 d d)]

/-- `r` into quadword 0 of `d`, zeros elsewhere. -/
def bcastLo (d : XReg) (r : Reg) : List Instr := [.vop (.vmovq d r)]

/-- `d_j = 5 Σ_{i > j} H_i Y_(5 + j - i) + Σ_{i ≤ j} H_i Y_(j - i)` (the
low doublewords of `Y`); the first product is written, the others added
through `tP`. -/
def prodJ (j : Nat) : List Instr :=
  if j < 4 then
    [v .vpmuludq (dreg j) (hreg (j + 1)) (yreg 4)] ++
    ((List.range (3 - j)).flatMap fun k =>
      [v .vpmuludq tP (hreg (j + 2 + k)) (yreg (3 - k)), v .vpaddq (dreg j) (dreg j) tP]) ++
    [sll tP (dreg j) 2, v .vpaddq (dreg j) (dreg j) tP] ++
    ((List.range (j + 1)).flatMap fun i =>
      [v .vpmuludq tP (hreg i) (yreg (j - i)), v .vpaddq (dreg j) (dreg j) tP])
  else
    [v .vpmuludq (dreg 4) (hreg 0) (yreg 4)] ++
    ((List.range 4).flatMap fun k =>
      [v .vpmuludq tP (hreg (k + 1)) (yreg (3 - k)), v .vpaddq (dreg 4) (dreg 4) tP])

/-- `H_j = d_j mod 2²⁶`, and its carry added to `d_(j+1)` (`j < 4`), with
the mask in `H₄`. -/
def carryJ (j : Nat) : List Instr :=
  [srl tP (dreg j) 26, v .vpand (hreg j) (dreg j) (hreg 4), v .vpaddq (dreg (j + 1)) (dreg (j + 1)) tP]

/-- `H = (d mod 2²⁶ each, carried)`: `d₀` to `d₄` carried in turn, `d₄`'s
carry times 5 added to `H₀`, and `H₀`'s carry to `H₁`. The mask is
broadcast from `r8` into `H₄`, then kept in `d₀` once `H₄` is written. -/
def carry : List Instr :=
  bcast (hreg 4) .r8 ++ carryJ 0 ++ carryJ 1 ++ carryJ 2 ++ carryJ 3 ++
  [srl tP (dreg 4) 26, .vop (.vmovdqa .l256 (dreg 0) (hreg 4)), v .vpand (hreg 4) (dreg 4) (hreg 4),
   sll (dreg 1) tP 2, v .vpaddq tP tP (dreg 1), v .vpaddq (hreg 0) (hreg 0) tP,
   srl tP (hreg 0) 26, v .vpand (hreg 0) (hreg 0) (dreg 0), v .vpaddq (hreg 1) (hreg 1) tP]

/-- `H = H · Y` (lane by lane, the low doublewords of `Y`). -/
def mul : List Instr :=
  prodJ 0 ++ prodJ 1 ++ prodJ 2 ++ prodJ 3 ++ prodJ 4 ++ carry

/-- The limbs of the 128-bit numbers `lo + 2⁶⁴ hi` (quadword by quadword)
into `d₀`–`d₄`, with `lo` in `d₀` and `hi` in `d₁`: `x mod 2²⁶` is
`(x << 38) >> 38`, so `d₀ = (lo << 38) >> 38`, `d₁ = (lo << 12) >> 38`,
`d₂ = lo >> 52 | (hi << 50) >> 38`, `d₃ = (hi << 24) >> 38`,
`d₄ = hi >> 40`. -/
def split : List Instr := [
  srl (dreg 4) (dreg 1) 40, sll (dreg 3) (dreg 1) 24, srl (dreg 3) (dreg 3) 38,
  sll (dreg 2) (dreg 1) 50, srl (dreg 2) (dreg 2) 38, srl tP (dreg 0) 52, v .vpor (dreg 2) (dreg 2) tP,
  sll (dreg 1) (dreg 0) 12, srl (dreg 1) (dreg 1) 38,
  sll (dreg 0) (dreg 0) 38, srl (dreg 0) (dreg 0) 38]

/-- The four blocks at `rsi` into `d` (block `k` in lane `k`), with the pad
bit (from `r9`), added to `H`. -/
def addGroup : List Instr :=
  [.vmovdquLoad .l256 (dreg 2) (at_ .rsi 0), .vmovdquLoad .l256 (dreg 3) (at_ .rsi 32),
   v .vpunpcklqdq (dreg 0) (dreg 2) (dreg 3), v .vpunpckhqdq (dreg 1) (dreg 2) (dreg 3),
   .vop (.vpermq (dreg 0) (dreg 0) 0xd8), .vop (.vpermq (dreg 1) (dreg 1) 0xd8)] ++ split ++
  bcast tP .r9 ++ [v .vpor (dreg 4) (dreg 4) tP] ++
  (List.range 5).map fun i => v .vpaddq (hreg i) (hreg i) (dreg i)

/-- `r` (clamped, from the key) in every lane of `H`. -/
def loadR : List Instr := [
  .movImm64 .rax 0x0ffffffc0fffffff, .mov .r10 (.mem (at_ .rdi 24)), .alu .and .r10 (.reg .rax),
  .movImm64 .rax 0x0ffffffc0ffffffc, .mov .r11 (.mem (at_ .rdi 32)), .alu .and .r11 (.reg .rax)] ++
  bcast (dreg 0) .r10 ++ bcast (dreg 1) .r11 ++ split ++
  (List.range 5).map fun i => .vop (.vmovdqa .l256 (hreg i) (dreg i))

/-- `Y = H` in both doublewords of each quadword. -/
def initY : List Instr :=
  (List.range 5).flatMap fun i => [sll tP (hreg i) 32, v .vpor (yreg i) (hreg i) tP]

/-- The doublewords of `Y` that `sel` selects replaced by those of
`H << 32`, or (with `lo`) of `H << 32 | H`. -/
def blendY (sel : BitVec 8) (lo : Bool) : List Instr :=
  (List.range 5).flatMap fun i =>
    [sll tP (hreg i) 32] ++ (if lo then [v .vpor tP tP (hreg i)] else []) ++
    [.vop (.vpblendd .l256 (yreg i) (yreg i) tP sel)]

/-- The accumulator `h` (from the state) in lane 0 of `H`, zeros elsewhere:
its words into `r10`, `r11` and `rax`, then limb 4 is `(h₁ >> 40) | (h₂ << 24)`. -/
def loadHw : List Instr :=
  [.mov .r10 (.mem (at_ .rdi 0)), .mov .r11 (.mem (at_ .rdi 8)), .mov .rax (.mem (at_ .rdi 16))]
def loadH : List Instr :=
  bcastLo (dreg 0) .r10 ++ bcastLo (dreg 1) .r11 ++ split ++
  [.vop (.vmovq tP .rax), sll tP tP 24, v .vpor (dreg 4) (dreg 4) tP] ++
  (List.range 5).map fun i => .vop (.vmovdqa .l256 (hreg i) (dreg i))

/-- The mask and the pad bit, in `r8` and `r9`. -/
def consts : List Instr := [.mov32 .r8 (.imm 0x3ffffff), .mov32 .r9 (.imm 0x1000000)]

/-- Intel's MCDT prologue and epilogue, with MXCSR saved at `[rdi + 120]`
(bits 31:16 cleared) and `0x1FBF` at `[rdi + 124]`. -/
def mxcsrIn : List Instr := [
  .stmxcsr (at_ .rdi 120), .mov32 .rax (.mem (at_ .rdi 120)), .alu32 .and .rax (.imm 0xffff),
  .store32 (at_ .rdi 120) .rax, .mov32 .rax (.imm 0x1FBF), .store32 (at_ .rdi 124) .rax,
  .ldmxcsr (at_ .rdi 124), .lfence]
def mxcsrOut : List Instr := [.lfence, .ldmxcsr (at_ .rdi 120)]

/-- `Y`: `r` in both doublewords, then `r²`, `r³` and `r⁴` blended into
the high doublewords of lanes 0–2, 0–1 and 0, and `r⁴` into every low
doubleword. -/
def powers : List Instr :=
  loadR ++ initY ++ mul ++ blendY 0x2A false ++ mul ++ blendY 0x0A false ++ mul ++ blendY 0x57 true

/-- One group of four blocks, multiplied by `r⁴`. -/
def groupBody : Prog isa :=
  .block (addGroup ++ mul ++ [.alu .add .rsi (.imm 64), .alu .sub .rcx (.imm 1)])

/-- The last group, multiplied lane by lane by the high doublewords of `Y`. -/
def last : List Instr :=
  addGroup ++ (List.range 5).map (fun i => srl (yreg i) (yreg i) 32) ++ mul

/-- The sum of the lanes of `H` into `d`, carried into `H`. -/
def sumLanes : List Instr :=
  (List.range 5).flatMap (fun i =>
    [.vop (.vpermq tP (hreg i) 0x4e), v .vpaddq (dreg i) (hreg i) tP,
     v .vpunpckhqdq tP (dreg i) (dreg i), v .vpaddq (dreg i) (dreg i) tP]) ++ carry

/-- `h` (lane 0 of `H`) carried from `h₁` to `h₄`, with the mask in `d₀`:
then every limb is below `2²⁶` but `h₄`, which is at most `2²⁶`. -/
def fullCarry : List Instr :=
  bcast (dreg 0) .r8 ++ (List.range 3).flatMap fun i =>
    [srl tP (hreg (i + 1)) 26, v .vpand (hreg (i + 1)) (hreg (i + 1)) (dreg 0),
     v .vpaddq (hreg (i + 2)) (hreg (i + 2)) tP]

/-- 5 and `2²⁷ - 1`, for `reduce`. -/
def consts2 : List Instr := [.mov32 .rax (.imm 5), .mov32 .r10 (.imm 0x7ffffff)]

/-- `g = h + 5` (`Y`), carried, and `h` replaced by `g - 2¹³⁰` if that is
not negative (if `g₄ ≥ 2²⁶`): `h mod p`. The mask `2²⁷ - 1` or 0 (which
clears every limb of `h`, whose `h₄` may be `2²⁶`) is
`(g₄ >> 26) · (2²⁷ - 1)`, in `tP`; `rax` holds 5, and `r10` `2²⁷ - 1`. -/
def reduce : List Instr :=
  bcast tP .rax ++ [v .vpaddq (yreg 0) (hreg 0) tP] ++
  ((List.range 4).flatMap fun j =>
    [srl tP (yreg j) 26, v .vpand (yreg j) (yreg j) (dreg 0), v .vpaddq (yreg (j + 1)) (hreg (j + 1)) tP]) ++
  [srl tP (yreg 4) 26, v .vpand (yreg 4) (yreg 4) (dreg 0)] ++ bcast (dreg 1) .r10 ++
  [v .vpmuludq tP tP (dreg 1)] ++
  (List.range 5).flatMap fun i =>
    [v .vpand (yreg i) (yreg i) tP, v .vpandn (hreg i) tP (hreg i), v .vpor (hreg i) (hreg i) (yreg i)]

/-- The words `w₀ = h₀ | h₁ << 26 | h₂ << 52` (`d₁`), `w₁ = h₂ >> 12 | h₃ << 14 | h₄ << 40`
(`d₂`) and `w₂ = h₄ >> 24` (`d₃`) of lane 0, stored in the state as
`w₀, w₁` at 0 and `w₁, w₂` at 8. -/
def storeH : List Instr := [
  sll (dreg 1) (hreg 1) 26, sll (dreg 2) (hreg 2) 52, v .vpor (dreg 1) (dreg 1) (hreg 0),
  v .vpor (dreg 1) (dreg 1) (dreg 2),
  srl (dreg 2) (hreg 2) 12, sll (dreg 3) (hreg 3) 14, v .vpor (dreg 2) (dreg 2) (dreg 3),
  sll (dreg 3) (hreg 4) 40, v .vpor (dreg 2) (dreg 2) (dreg 3),
  srl (dreg 3) (hreg 4) 24,
  v .vpunpcklqdq tP (dreg 1) (dreg 2), .vmovdquStore .l128 (at_ .rdi 0) tP,
  v .vpunpcklqdq tP (dreg 2) (dreg 3), .vmovdquStore .l128 (at_ .rdi 8) tP]

/-- The first `4 ⌊n / 4⌋` blocks absorbed; `rsi` advanced past them,
`rdx = n mod 4`. The groups before the last are counted down in `rcx`. -/
def body : Prog isa :=
  .seq (.block (consts ++ mxcsrIn ++ powers ++ loadHw ++ loadH ++
    [.mov .rcx (.reg .rdx), .shift .shr .rcx 2, .alu .sub .rcx (.imm 1)]))
  (.seq (.loop groupBody .ne)
    (.block (consts2 ++ last ++ sumLanes ++ fullCarry ++ reduce ++ mxcsrOut ++ storeH ++
      [.vop .vzeroupper, .alu .add .rsi (.imm 64), .alu .and .rdx (.imm 3)])))

def scalar : Prog isa := .call "vg_poly1305_blocks" blocks

def blocksAvx2 : Prog isa :=
  .seq (.block [.alu .cmp .rdx (.imm (BitVec.ofNat 32 minBlocks))])
    (.ite .b scalar
      (.seq body
        (.seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) scalar))))

end VG.Impl.Poly1305.X86_64.Avx2
