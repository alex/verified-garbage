import VerifiedGarbage.Spec.Md5
import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Impl.Md5.X86_64

/-!
# MD5 compression function: x86-64 implementation with AVX-512

`vg_md5_compress_avx512(state = rdi, blocks = rsi, n = rdx, scratch = rcx)`,
with the scalar implementation's interface and contract
(`Impl/Md5/X86_64.lean`), for CPUs with AVX512F and AVX512VL.

* The MD buffer `A, B, C, D` lives in doubleword 0 of four `xmm` registers
  (the other doublewords are unused), loaded once before the first block and
  kept there between blocks. As in the scalar code, the fully unrolled
  operations rename them: in operation `t`, word `k` of the specification's
  `(a, b, c, d)` is in `var t k`.
* `vpternlogd` computes each round's auxiliary function in one instruction
  (its `imm8` is the function's truth table, `tern`), and `vprold` rotates,
  so on the path from one operation's `b` to the next's are four
  instructions in every round: `vpternlogd`, the addition into `a`, the
  rotation and the addition of `b`.
* `X[k] + T[t+1]` is computed in `r11` (a little-endian 32-bit load from the
  block and an addition) and moved to `xmm5` by `vmovq`, off that path.
* Between blocks the four words are gathered into one register
  (`vpunpckldq`, `vpunpcklqdq`), added to the MD buffer in memory, stored,
  and spread out again (`vpshufd`).
* Only caller-saved registers are used (`r11`, `xmm0–xmm5` and the argument
  registers), so nothing is saved, and `scratch` is not used. Every vector
  instruction is `VEX.128` or `EVEX.128`, which zero the upper bits of
  their destination.
* `rdi, rsi, rdx, rcx` (the pointers and the block count) are public; no
  address and no branch depends on anything else.
-/

namespace VG.Impl.Md5.X86_64.Avx512

open VG.X86_64
open VG.Spec.Md5 (ks Ts)
open VG.Impl.Md5.X86_64 (at_ rot advance)

/-- The registers holding the MD buffer. -/
def work : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3]

/-- The register holding word `k` (`a = 0, …, d = 3`) at the start of operation `t`. -/
def var (t k : Nat) : XReg := work.getD ((k + 4 - t % 4) % 4) .xmm0

/-- The auxiliary function's value. -/
def T0 : XReg := .xmm4

/-- `X[k] + T[t+1]`. -/
def XK : XReg := .xmm5

/-- The general-purpose register `X[k] + T[t+1]` is computed in. -/
def R : Reg := .r11

/-- The `imm8` of `vpternlogd T0, b, c` (with `d` in `T0`) computing the
auxiliary function of round `r`: bit `4 d + 2 b + c` is the function's
value. -/
def tern : Nat → BitVec 8
  | 0 => 0xb8
  | 1 => 0xca
  | 2 => 0x96
  | _ => 0x65

/-- Operation `t`: `a := b + ((a + (X[k] + T[t+1]) + fn(b,c,d)) <<< s)`. -/
def step (t : Nat) : List Instr :=
  let a := var t 0; let b := var t 1; let c := var t 2; let d := var t 3
  [.mov32 R (.mem (at_ .rsi (4 * ks.getD t 0))), .alu32 .add R (.imm (Ts.getD t 0)),
    .vop (.vmovq XK R), .vop (.vbin .vpaddd .l128 a a XK),
    .vop (.vmovdqa .l128 T0 d), .vop (.vpternlogd .l128 T0 b c (tern (t / 16))),
    .vop (.vbin .vpaddd .l128 a a T0),
    .vop (.vprold .l128 a a (BitVec.ofNat 8 (rot t))), .vop (.vbin .vpaddd .l128 a a b)]

/-- Operations `0 … n-1`. -/
def steps : Nat → Prog isa
  | 0 => .block []
  | n + 1 => .seq (steps n) (.block (step n))

/-- Spread the MD buffer in `xmm0` out: word `k` to doubleword 0 of `var 0 k`
(`64 % 4 = 0`, so the words are in the same registers after the 64
operations). -/
def spread : List Instr :=
  [.vop (.vpshufd .l128 .xmm1 .xmm0 0x55), .vop (.vpshufd .l128 .xmm2 .xmm0 0xaa),
    .vop (.vpshufd .l128 .xmm3 .xmm0 0xff)]

/-- Load the MD buffer. -/
def load : List Instr := .vmovdquLoad .l128 .xmm0 (at_ .rdi 0) :: spread

/-- Add the words into the MD buffer, which they then hold for the next block. -/
def update : List Instr :=
  [.vop (.vbin .vpunpckldq .l128 .xmm4 .xmm0 .xmm1), .vop (.vbin .vpunpckldq .l128 .xmm5 .xmm2 .xmm3),
    .vop (.vbin .vpunpcklqdq .l128 .xmm4 .xmm4 .xmm5), .vmovdquLoad .l128 .xmm5 (at_ .rdi 0),
    .vop (.vbin .vpaddd .l128 .xmm0 .xmm4 .xmm5), .vmovdquStore .l128 (at_ .rdi 0) .xmm0] ++ spread

/-- One block. -/
def body : Prog isa := .seq (steps 64) (.block (update ++ advance))

def compress : Prog isa :=
  .seq (.block [.alu .test .rdx (.reg .rdx)]) (.ite .e (.block []) (.seq (.block load) (.loop body .ne)))

end VG.Impl.Md5.X86_64.Avx512
