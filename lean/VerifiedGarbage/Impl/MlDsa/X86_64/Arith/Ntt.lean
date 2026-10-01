import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Vec
import VerifiedGarbage.Spec.MlDsa

/-!
# ML-DSA on x86-64: `vg_mldsa_ntt` and `vg_mldsa_inv_ntt`

`ntt(f = rdi, scratch = rsi)` and `nttInv(f = rdi, scratch = rsi)` compute
on four coefficients of `f` at a time, in place, as doublewords of SSE
registers (see `Vec.lean`). `scratch` holds the 256 `u32`s
`ζ^BitRev8(m) · 2³² mod q` (`zmTab`, stored with immediates: the code has
no other memory), and MXCSR's at bytes 768 to 775 before and after
(`withMxcsr`, which saves the caller's MXCSR in `r11` in between).

Within `withMxcsr`, the prologue stores the table and the constants. Then
the layers, each a pass over `f` with `rdx` pointing at the coefficients it
loads and `r8` at the zetas of the table:

* `NTT` (Algorithm 41): the layers with `len` = 128, 64, 32, 16, 8 and 4
  (`vlay`) run their blocks (counted in `rax`), each its zeta in the
  doublewords of `xmm13` (`vzeta`), and `len / 4` times the butterflies of
  four coefficients `w[j]` and of the four `w[j + len]` (`vbfly`, counted
  in `rcx`). The layer with `len = 2` (`vlay2`) loads the 8 coefficients of
  two blocks, gathers their lower and upper halves into `xmm0` and `xmm1`
  (`punpcklqdq`, `punpckhqdq`), with the two zetas in the halves of
  `xmm13`; the layer with `len = 1` (`vlay1`) those of four blocks, their
  pairs gathered (with `pshufd` first), with the four zetas in the
  doublewords of `xmm13`.
* `NTT⁻¹` (Algorithm 42): the same layers in the opposite order, with the
  zetas from `m = 255` down and the inverse butterflies (`vibfly`); then
  every coefficient is multiplied by `8347681 = 256⁻¹ mod q` (`vscale`,
  with `vmont` by `8347681 · 2³² mod q = 16382`).

Every address and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov withMxcsr rcxLoop)

/-- `ζ^BitRev8(m) · 2³² mod q`. -/
def zmTab (m : Nat) : Nat := 1753 ^ Spec.MlDsa.bitRev8 m * 2 ^ 32 % 8380417

/-- `d ← r + off`. -/
def leaR (d r : Reg) (off : Nat) : List Instr := [.mov d (.reg r), .alu .add d (.imm (BitVec.ofNat 32 off))]

/-- The zetas at `[r8]` in the doublewords of `xmm13`, arranged by `pshufd`
with `o`, and its odd doublewords in the even ones of `xmm12`. -/
def vzeta (o : BitVec 8) : List Instr :=
  [.movdquLoad .xmm13 (at_ .r8 0), .xop (.pshufd .xmm13 .xmm13 o), .xop (.pshufd .xmm12 .xmm13 0xF5)]

/-- A layer with `len ≥ 4` and butterflies `bf`: its `128 / len` blocks, the
first with the zeta `k`, the zeta pointer moving by `dz` bytes. -/
def vlay (bf : List Instr) (len k : Nat) (dz : BitVec 32) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ leaR .r8 .rsi (4 * k) ++
    [.mov32 .rax (.imm (BitVec.ofNat 32 (128 / len)))])) <|
  .loop (.seq (.block (vzeta 0 ++ [.alu .add .r8 (.imm dz)]))
    (.seq (rcxLoop (len / 4) ([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx (4 * len))] ++
        bf ++ [.movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx (4 * len)) .xmm3,
          .alu .add .rdx (.imm 16)]))
      (.block [.alu .add .rdx (.imm (BitVec.ofNat 32 (4 * len))), .alu .sub .rax (.imm 1)]))) .ne

/-- The layer with `len = 2`, two blocks at a time: the zetas at `[r8]`
arranged by `pshufd` with `o`, the zeta pointer moving by `dz` bytes. -/
def vlay2 (bf : List Instr) (k : Nat) (o : BitVec 8) (dz : BitVec 32) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ leaR .r8 .rsi (4 * k))) <|
  rcxLoop 32 ([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm1 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), xmov .xmm2 .xmm0, xb .punpcklqdq .xmm0 .xmm1, xb .punpckhqdq .xmm2 .xmm1,
      xmov .xmm1 .xmm2] ++ bf ++
    [xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm3, xb .punpckhqdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)])

/-- The layer with `len = 1`, four blocks at a time: the zetas at `[r8]`
arranged by `pshufd` with `o`, the zeta pointer moving by `dz` bytes. -/
def vlay1 (bf : List Instr) (k : Nat) (o : BitVec 8) (dz : BitVec 32) : Prog isa :=
  .seq (.block ([.mov .rdx (.reg .rdi)] ++ leaR .r8 .rsi (4 * k))) <|
  rcxLoop 32 ([.movdquLoad .xmm0 (at_ .rdx 0), .movdquLoad .xmm2 (at_ .rdx 16)] ++ vzeta o ++
    [.alu .add .r8 (.imm dz), .xop (.pshufd .xmm0 .xmm0 0xD8), .xop (.pshufd .xmm2 .xmm2 0xD8),
      xmov .xmm1 .xmm0, xb .punpcklqdq .xmm0 .xmm2, xb .punpckhqdq .xmm1 .xmm2] ++ bf ++
    [xmov .xmm1 .xmm0, xb .punpckldq .xmm0 .xmm3, xb .punpckhdq .xmm1 .xmm3,
      .movdquStore (at_ .rdx 0) .xmm0, .movdquStore (at_ .rdx 16) .xmm1, .alu .add .rdx (.imm 32)])

/-- Every coefficient times `8347681 = 256⁻¹ mod q`, reduced. -/
def vscale : Prog isa :=
  .seq (.block [.mov .rdx (.reg .rdi), .mov32 .rax (.imm 16382), .xop (.movq .xmm13 .rax),
      .xop (.pshufd .xmm13 .xmm13 0), xmov .xmm12 .xmm13])
    (rcxLoop 64 ([.movdquLoad .xmm3 (at_ .rdx 0)] ++ vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++
      vcsub .xmm3 .xmm2 ++ [.movdquStore (at_ .rdx 0) .xmm3, .alu .add .rdx (.imm 16)]))

/-- The table and the constants. -/
def vpro : List Instr := dwordTab zmTab 256 .rsi ++ vconsts

def ntt : Prog isa := withMxcsr .rsi 768 <|
  .seq (.block vpro) (.seq (vlay vbfly 128 1 4) (.seq (vlay vbfly 64 2 4) (.seq (vlay vbfly 32 4 4)
    (.seq (vlay vbfly 16 8 4) (.seq (vlay vbfly 8 16 4) (.seq (vlay vbfly 4 32 4)
      (.seq (vlay2 vbfly 64 0x50 8) (vlay1 vbfly 128 0xE4 16))))))))

def nttInv : Prog isa := withMxcsr .rsi 768 <|
  .seq (.block vpro) (.seq (vlay1 vibfly 252 0x1B (-16)) (.seq (vlay2 vibfly 126 0x05 (-8))
    (.seq (vlay vibfly 4 63 (-4)) (.seq (vlay vibfly 8 31 (-4)) (.seq (vlay vibfly 16 15 (-4))
      (.seq (vlay vibfly 32 7 (-4)) (.seq (vlay vibfly 64 3 (-4)) (.seq (vlay vibfly 128 1 (-4))
        vscale))))))))

end VG.Impl.MlDsa.X86_64.Arith
