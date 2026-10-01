import VerifiedGarbage.Impl.MlKem.X86_64.Ntt
import VerifiedGarbage.Impl.MlKem.X86_64.Avx

/-!
# ML-KEM on x86-64: `vg_mlkem_ntt_avx2` and `vg_mlkem_inv_ntt_avx2`

`nttAvx2(f = rdi, scratch = rsi)` and `nttInvAvx2(f = rdi, scratch = rsi)`
are `vg_mlkem_ntt` and `vg_mlkem_inv_ntt` (`Ntt.lean`) on sixteen
coefficients at a time, eight in each 128-bit lane of AVX2 registers
(`Avx.lean`), with the same working space: the table of zetas at 0, the
polynomial as 256 words at 256 (`S`), and MXCSR's at 768 (`withMxcsr`).
The prologue packs `f` into `S` sixteen coefficients at a time (`ypack`:
`vpackssdw` and `vpermq` to put the words back in order), and the epilogue
unpacks `S` into `f` (`yunpack`).

The table holds `ζ^BitRev7(k) · 2¹⁶ mod q` at `k` for `NTT` (`zmTab`), and
at `127 - k` for `NTT⁻¹` (`zmTabInv`), so that both take the zetas of their
blocks in increasing order: a layer whose first block has the zeta at
position `t` of the table runs them in order from `r8` at `t`. The layers,
each a pass over `S` with `rdx` at the words it loads:

* `len ≥ 16` (`ylay`): each block with its zeta in every word of `ymm13`
  (`yzeta1`), and `len / 16` times the butterflies of the sixteen words
  `f[j]` and the sixteen `f[j + len]`;
* `len = 8` (`ylay8`): two blocks at a time (32 words, two loads), their
  lower halves gathered into `ymm0` and upper halves into `ymm1` by
  `vperm2i128`, with the two zetas in the lanes of `ymm13` (`yzeta2`);
* `len = 4` and `len = 2` (`ylay4`, `ylay2`): in each lane, what
  `vlay4` and `vlay2` do to `xmm0` and `xmm1` (`Ntt.lean`), with lane `l`
  of the two loads of 32 words holding the words `8l` to `8l + 7` and
  `16 + 8l` to `16 + 8l + 7`; the zetas of the blocks of each lane are
  gathered into the lanes of `ymm13` with `vpblendd` (`yzeta4`, `yzeta8`).

`NTT⁻¹` then multiplies every coefficient by `3303` (`yscale`). Both clear
the upper halves of the vector registers before returning (`vzeroupper`).
Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `ζ^BitRev7(127 - k) · 2¹⁶ mod q`, the table of `NTT⁻¹`. -/
def zmTabInv (k : Nat) : Nat := zmTab (127 - k)

/-- `vop d, a, b` on 256-bit registers. -/
def yb (op : VBinOp) (d a b : XReg) : Instr := .vop (.vbin op .l256 d a b)

/-- The zeta at `[r8]` in every word of `ymm13`: `vzeta 0` (`Ntt.lean`) in each lane. -/
def yzeta1 : List Instr :=
  .vbroadcasti128 .xmm13 (at_ .r8 0) :: toY [xb .punpcklwd .xmm13 .xmm13, .xop (.pshufd .xmm13 .xmm13 0)]

/-- The zetas `z₀, z₁, …` at `[r8]`, doubled into the doublewords of each lane of `ymm13`
(`vpunpcklwd`), arranged by `vpshufd` with `o₀` into `ymm13` and with `o₁` into `ymm2`,
and lane 0 of the former with lane 1 of the latter (`vpblendd`). -/
def yzetaS (o₀ o₁ : BitVec 8) : List Instr :=
  .vbroadcasti128 .xmm13 (at_ .r8 0) ::
    toY [xb .punpcklwd .xmm13 .xmm13, .xop (.pshufd .xmm2 .xmm13 o₁), .xop (.pshufd .xmm13 .xmm13 o₀)] ++
    [.vop (.vpblendd .l256 .xmm13 .xmm13 .xmm2 0xF0)]

/-- The zetas at `[r8]` and `[r8 + 2]` in every word of lane 0 and of lane 1 of `ymm13`. -/
def yzeta2 : List Instr := yzetaS 0x00 0x55

/-- The four zetas from `[r8]`: in the halves of lane 0 of `ymm13` the first and
the third, and in those of lane 1 the second and the fourth. -/
def yzeta4 : List Instr := yzetaS 0xA0 0xF5

/-- The eight zetas `z₀, …, z₇` from `[r8]`, doubled into doublewords: `z₀, z₁, z₄, z₅`
in lane 0 of `ymm13`, and `z₂, z₃, z₆, z₇` in lane 1. -/
def yzeta8 : List Instr :=
  .vbroadcasti128 .xmm2 (at_ .r8 0) ::
    toY [xmov .xmm1 .xmm2, xb .punpcklwd .xmm1 .xmm2, xb .punpckhwd .xmm2 .xmm2, xmov .xmm13 .xmm1,
      xb .punpcklqdq .xmm13 .xmm2, xb .punpckhqdq .xmm1 .xmm2] ++
    [.vop (.vpblendd .l256 .xmm13 .xmm13 .xmm1 0xF0)]

/-- A layer with `len ≥ 16` and butterflies `bf`: its `128 / len` blocks, the
first with the zeta at position `t` of the table. -/
def ylay (bf : List Instr) (len t : Nat) : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * t) ++
    [.mov32 .rax (.imm (BitVec.ofNat 32 (128 / len)))])) <|
  .loop (.seq (.block (yzeta1 ++ [.alu .add .r8 (.imm 2)]))
    (.seq (rcxLoop (len / 16) ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0),
        .vmovdquLoad .l256 .xmm1 (at_ .rdx (2 * len))] ++ toY bf ++
        [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx (2 * len)) .xmm3,
          .alu .add .rdx (.imm 32)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (2 * len))), .alu .sub .rax (.imm 1)]))) .ne

/-- The layer with `len = 8`, two blocks at a time, the first with the zeta
at position `t` of the table. -/
def ylay8 (bf : List Instr) (t : Nat) : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * t))) <|
  rcxLoop 8 ([.vmovdquLoad .l256 .xmm4 (at_ .rdx 0), .vmovdquLoad .l256 .xmm5 (at_ .rdx 32)] ++ yzeta2 ++
    [.alu .add .r8 (.imm 4), .vop (.vperm2i128 .xmm0 .xmm4 .xmm5 0x20), .vop (.vperm2i128 .xmm1 .xmm4 .xmm5 0x31)] ++
    toY bf ++
    [.vop (.vperm2i128 .xmm4 .xmm0 .xmm3 0x20), .vop (.vperm2i128 .xmm5 .xmm0 .xmm3 0x31),
      .vmovdquStore .l256 (at_ .rdx 0) .xmm4, .vmovdquStore .l256 (at_ .rdx 32) .xmm5, .alu .add .rdx (.imm 64)])

/-- `vlay4`'s gathering of the lower and the upper halves (`Ntt.lean`), from
`xmm0` and `xmm4` to `xmm0` and `xmm1`. -/
def gath4 : List Instr := [xmov .xmm1 .xmm0, xb .punpckhqdq .xmm1 .xmm4, xb .punpcklqdq .xmm0 .xmm4]

/-- `vlay4`'s interleaving back, from `xmm0` and `xmm3` to `xmm0` and `xmm1`. -/
def scat4 : List Instr := [xmov .xmm1 .xmm0, xb .punpckhqdq .xmm1 .xmm3, xb .punpcklqdq .xmm0 .xmm3]

/-- `vlay2`'s gathering of the pairs, from `xmm0` and `xmm4` to `xmm0` and `xmm1`. -/
def gath2 : List Instr :=
  [.xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm4 .xmm4 0xD8), xmov .xmm1 .xmm0,
    xb .punpckhqdq .xmm1 .xmm4, xb .punpcklqdq .xmm0 .xmm4]

/-- `vlay2`'s interleaving back, from `xmm0` and `xmm3` to `xmm0` and `xmm1`. -/
def scat2 : List Instr := [xmov .xmm1 .xmm0, xb .punpckhdq .xmm1 .xmm3, xb .punpckldq .xmm0 .xmm3]

/-- The layer with `len = 4` or `len = 2` (`gath`, `scat`), four or eight
blocks at a time with the zetas `zeta` (moving `r8` by `dz` bytes), the
first with the zeta at position `t` of the table. -/
def ylay42 (bf gath scat zeta : List Instr) (dz : BitVec 32) (t : Nat) : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ leaR .r8 .rsi (2 * t))) <|
  rcxLoop 8 ([.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vmovdquLoad .l256 .xmm4 (at_ .rdx 32)] ++ zeta ++
    [.alu .add .r8 (.imm dz)] ++ toY (gath ++ bf ++ scat) ++
    [.vmovdquStore .l256 (at_ .rdx 0) .xmm0, .vmovdquStore .l256 (at_ .rdx 32) .xmm1, .alu .add .rdx (.imm 64)])

def ylay4 (bf : List Instr) (t : Nat) : Prog isa := ylay42 bf gath4 scat4 yzeta4 8 t

def ylay2 (bf : List Instr) (t : Nat) : Prog isa := ylay42 bf gath2 scat2 yzeta8 16 t

/-- Every word of `S` times `3303`, reduced. -/
def yscale : Prog isa :=
  .seq (.block (leaR .rdx .rsi oS ++ yconst .xmm13 0x02000200))
    (rcxLoop 16 ([.vmovdquLoad .l256 .xmm3 (at_ .rdx 0)] ++ toY (vmont .xmm3 .xmm13 .xmm2 ++ vcadd .xmm3 .xmm2) ++
      [.vmovdquStore .l256 (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 32)]))

/-- The 256 `u32`s at `[r9]` to words at `[rdx]`, sixteen at a time. -/
def ypack : Prog isa :=
  rcxLoop 16 [.vmovdquLoad .l256 .xmm0 (at_ .r9 0), .vmovdquLoad .l256 .xmm1 (at_ .r9 32),
    yb .vpackssdw .xmm0 .xmm0 .xmm1, .vop (.vpermq .xmm0 .xmm0 0xD8), .vmovdquStore .l256 (at_ .rdx 0) .xmm0,
    .alu .add .r9 (.imm 64), .alu .add .rdx (.imm 32)]

/-- The 256 words at `[rdx]` to `u32`s at `[r9]`, sixteen at a time. -/
def yunpack : Prog isa :=
  .seq (.block [yb .vpxor .xmm4 .xmm4 .xmm4])
    (rcxLoop 16 [.vmovdquLoad .l256 .xmm0 (at_ .rdx 0), .vop (.vpermq .xmm0 .xmm0 0xD8),
      yb .vpunpckhwd .xmm1 .xmm0 .xmm4, yb .vpunpcklwd .xmm0 .xmm0 .xmm4,
      .vmovdquStore .l256 (at_ .r9 0) .xmm0, .vmovdquStore .l256 (at_ .r9 32) .xmm1,
      .alu .add .r9 (.imm 64), .alu .add .rdx (.imm 32)])

/-- The table `tab`, the constants, and `f` packed into `S`. -/
def ypro (tab : Nat → Nat) : Prog isa :=
  .seq (.block (wordTab tab 128 .rsi 0 ++ yconsts ++ [.mov .r9 (.reg .rdi)] ++ leaR .rdx .rsi oS)) ypack

/-- `S` unpacked into `f`, and the upper halves of the vector registers cleared. -/
def yepi : Prog isa :=
  .seq (.block ([.mov .r9 (.reg .rdi)] ++ leaR .rdx .rsi oS)) (.seq yunpack (.block [.vop .vzeroupper]))

def nttAvx2 : Prog isa := withMxcsr .rsi oMx <|
  .seq (ypro zmTab) (.seq (ylay vbfly 128 1) (.seq (ylay vbfly 64 2) (.seq (ylay vbfly 32 4)
    (.seq (ylay vbfly 16 8) (.seq (ylay8 vbfly 16) (.seq (ylay4 vbfly 32) (.seq (ylay2 vbfly 64) yepi)))))))

def nttInvAvx2 : Prog isa := withMxcsr .rsi oMx <|
  .seq (ypro zmTabInv) (.seq (ylay2 vibfly 0) (.seq (ylay4 vibfly 64) (.seq (ylay8 vibfly 96)
    (.seq (ylay vibfly 16 112) (.seq (ylay vibfly 32 120) (.seq (ylay vibfly 64 124)
      (.seq (ylay vibfly 128 126) (.seq yscale yepi))))))))

end VG.Impl.MlKem.X86_64
