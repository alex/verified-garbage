import VerifiedGarbage.Impl.Aes.X86_64.AesNi

/-!
# AES with VAES on x86-64: GCM's counter mode

`vg_aes_ctr32_vaes(schedule = rdi, rounds = rsi, counter = rdx, data = rcx, n = r8,
scratch = r9)`, with the contract of `vg_aes_ctr32` (`Spec.Gcm.ctr32Contract`),
for CPUs with VAES and AVX2 (and AES-NI and SSSE3, for the blocks left).

A 256-bit register holds two AES states, one in each 128-bit lane, and the
VEX.256 `vaesenc` and `vaesenclast` apply a round to each lane with the round
key in the same lane of their second source, which `vbroadcasti128` loads
into both lanes. Sixteen blocks are encrypted at a time (`ymm0`–`ymm7`), each
round key loaded once into `ymm8` and applied to all eight registers, as
`vg_aes_ctr32_aesni` does with eight. With fewer than sixteen blocks (as
AES-CMAC's single blocks), the function is `vg_aes_ctr32_aesni`'s code, which
needs no setup of the upper lanes.

The counter is kept as two GCM blocks (byte-reversed, as
`vg_aes_ctr32_aesni` keeps one): `CB` in lane 0 of `ymm9` and `inc₃₂(CB)`
in lane 1. `vpshufb` with the byte-reversal mask in both lanes of `ymm10`
turns the pair into the AES inputs of two blocks, and `vpaddd` with 2 in
doubleword 0 of each lane of `ymm12` advances both by two. Lane 0 of each
register is what `vg_aes_ctr32_aesni` keeps in it: after the sixteen-block
loop, `vzeroupper` clears the upper lanes (so that the SSE code that follows
pays no transition penalty), and the blocks left (fewer than 16) go through
`vg_aes_ctr32_aesni`'s loops (`AesNi.ctrTail`), eight and then one at a
time, with the counter in `xmm9`, the mask in `xmm10` and 1 in `xmm11`,
where it left them.

`scratch` is not used, and no callee-saved register is written. Every branch
and every address depends only on the pointers, `rounds` and `n`.
-/

namespace VG.Impl.Aes.X86_64.Vaes

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ revMask ctrTail)

/-- The 128-bit constant `c` into `x` (`VEX.128`, so the upper lane is
cleared), through `rax` and `xmm13`. -/
def const (x : XReg) (c : BitVec 128) : List Instr :=
  [.movImm64 .rax (c.extractLsb' 0 64), .vop (.vmovq x .rax),
   .movImm64 .rax (c.extractLsb' 64 64), .vop (.vmovq .xmm13 .rax),
   .vop (.vbin .vpunpcklqdq .l128 x x .xmm13)]

/-- A round key into both lanes of `k`, then `op b, b, k` for each block
register `b`. -/
def keyOpK (k : XReg) (regs : List XReg) (op : VBinOp) (a : MemOp) : List Instr :=
  .vbroadcasti128 k a :: regs.map fun b => .vop (.vbin op .l256 b b k)

/-- Round `j` (`1 ≤ j < Nr`) of each block, the round key in `k`. -/
def roundK (k : XReg) (regs : List XReg) (j : Nat) : List Instr := keyOpK k regs .vaesenc (at_ .rdi (16 * j))

/-- AES of both lanes of each block register, with `rounds` (10, 12 or 14) in
`rsi`, the key schedule at `rdi`, and its last round key at `r10`, the round
keys in `k`, and the instructions `g j` after round `j`. -/
def aesK (k : XReg) (regs : List XReg) (g : Nat → List Instr := fun _ => []) : Prog isa :=
  .seq (.block (keyOpK k regs .vpxor (at_ .rdi 0) ++
      (List.range 9).flatMap (fun j => roundK k regs (j + 1) ++ g (j + 1)) ++ [.alu .cmp .rsi (.imm 10)]))
    (.seq
      (.ite .e (.block [])
        (.seq (.block (roundK k regs 10 ++ roundK k regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (roundK k regs 12 ++ roundK k regs 13)))))
      (.block (keyOpK k regs .vaesenclast (at_ .r10 0))))

/-- The counter blocks: each block register gets the two counters (`c`),
byte-reversed with the mask in `m`, and both counters advance by two (`i`). -/
def ctrsK (c m i : XReg) : List XReg → List Instr
  | [] => []
  | b :: bs => [.vop (.vbin .vpshufb .l256 b c m), .vop (.vbin .vpaddd .l256 c c i)] ++ ctrsK c m i bs

/-- XOR block register `i` into the data blocks `base + 32 (j + i)` and the
next, through `t`. -/
def xorDataK (t : XReg) (base : Reg) : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => [.vmovdquLoad .l256 t (at_ base (32 * j)), .vop (.vbin .vpxor .l256 b b t),
      .vmovdquStore .l256 (at_ base (32 * j)) b] ++ xorDataK t base bs (j + 1)

/-- A round key into both lanes of `ymm8`, then `op b, b, ymm8` for each
block register `b`. -/
def keyOp (regs : List XReg) (op : VBinOp) (a : MemOp) : List Instr := keyOpK .xmm8 regs op a

/-- Round `j` (`1 ≤ j < Nr`) of each block. -/
def round (regs : List XReg) (j : Nat) : List Instr := roundK .xmm8 regs j

/-- AES of both lanes of each block register, with `rounds` (10, 12 or 14) in
`rsi`, the key schedule at `rdi`, and its last round key at `r10`. -/
def aes (regs : List XReg) : Prog isa := aesK .xmm8 regs

/-- The counter blocks: each block register gets the two counters (`ymm9`),
byte-reversed, and both counters advance by two. -/
def ctrs (regs : List XReg) : List Instr := ctrsK .xmm9 .xmm10 .xmm12 regs

/-- XOR block register `i` into the data blocks `rcx + 32 (j + i)` and the
next. -/
def xorData (regs : List XReg) (j : Nat) : List Instr := xorDataK .xmm8 .rcx regs j

def regs8 : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7]

/-- Sixteen blocks. -/
def body16 : Prog isa :=
  .seq (.block (ctrs regs8))
    (.seq (aes regs8)
      (.block (xorData regs8 0 ++ [.alu .add .rcx (.imm 256), .alu .sub .r8 (.imm 16),
        .alu .cmp .r8 (.imm 16)])))

def ctrLoad : List Instr :=
  const .xmm10 revMask ++ [.vop (.vinserti128 .xmm10 .xmm10 .xmm10 1)] ++
  [.movImm64 .rax 1, .vop (.vmovq .xmm11 .rax),
   .movImm64 .rax 2, .vop (.vmovq .xmm12 .rax), .vop (.vinserti128 .xmm12 .xmm12 .xmm12 1),
   .vmovdquLoad .l128 .xmm9 (at_ .rdx 0), .vop (.vbin .vpshufb .l128 .xmm9 .xmm9 .xmm10),
   .vop (.vbin .vpaddd .l128 .xmm13 .xmm9 .xmm11), .vop (.vinserti128 .xmm9 .xmm9 .xmm13 1),
   .mov .r10 (.reg .rsi), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10),
   .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .r10), .alu .add .r10 (.reg .rdi)]

def ctr32 : Prog isa :=
  .seq (.block [.alu .cmp .r8 (.imm 16)])
    (.ite .b AesNi.ctr32
      (.seq (.block ctrLoad)
        (.seq (.loop body16 .ae)
          (.seq (.block [.vop .vzeroupper, .alu .cmp .r8 (.imm 8)]) ctrTail))))

end VG.Impl.Aes.X86_64.Vaes
