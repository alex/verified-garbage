import VerifiedGarbage.Impl.MlDsa.X86_64.Arith.Common
import VerifiedGarbage.Impl.MlKem.X86_64.Vec

/-!
# ML-DSA on x86-64: arithmetic modulo `q` in the doublewords of SSE registers

The NTT and its inverse compute on four coefficients at a time, as the
doublewords of SSE2 registers, with `q` in the doublewords of `xmm15` and
`-q⁻¹ mod 2³² = 4236238847` in those of `xmm14` (`vconsts`).

* `vmont d z zo t u`: `d ← d · z · 2⁻³² mod q`, in `[0, 2q)`, for any
  doublewords `d` and `z < q` (a Montgomery reduction). `pmuludq` multiplies
  the even doublewords of its operands into quadwords, so the even
  doublewords of `d` are multiplied by those of `z`, and the odd ones,
  moved to the even places of `u` by `pshufd`, by the even doublewords of
  `zo`, which hold the odd doublewords of `z` (`pshufd` with `0xF5`). For
  each product `P < 2³² · q`, `m = (P mod 2³²) · (-q⁻¹) mod 2³²` makes
  `P + m · q` a multiple of `2³²` (with `pmuludq` by `xmm14`, then by
  `xmm15`, which use the low doubleword of the product), less than `2⁶⁴`,
  and its high doubleword is `(P + m · q) / 2³² < 2q`, congruent to
  `P · 2⁻³²` modulo `q`. The quotients of the even doublewords are moved
  down to their places by `psrlq`; those of the odd ones are in place, and
  the low doublewords of their quadwords are 0, so `por` merges them.
* `vcadd d t`: `d ← d + q` for the doublewords of `d` that are negative
  (with `psrad` by 31, a mask), from `(-q, q)` to `[0, q)`; `vcsub d t`:
  `d ← d - q`, then `vcadd`, from `[0, 2q)` to `[0, q)`.

A coefficient `x` is multiplied by `ζ` as `vmont` with `ζ · 2³² mod q`,
which the tables hold.

`pmuludq` has data-dependent timing on processors with MCDT unless MXCSR is
`0x1FBF` (see `TCB/X86_64/Isa.lean`): the functions run inside ML-KEM's
`withMxcsr`.
-/

namespace VG.Impl.MlDsa.X86_64.Arith

open VG.X86_64
open VG.Impl.MlKem.X86_64 (xb xmov)

/-- `q` in the doublewords of `xmm15` and `-q⁻¹ mod 2³² = 4236238847` in
those of `xmm14`, through `rax`. -/
def vconsts : List Instr :=
  [.mov32 .rax (.imm 8380417), .xop (.movq .xmm15 .rax), .xop (.pshufd .xmm15 .xmm15 0),
    .mov32 .rax (.imm 4236238847), .xop (.movq .xmm14 .rax), .xop (.pshufd .xmm14 .xmm14 0)]

/-- The Montgomery reductions of the quadword products in `d`, with a
temporary `t`: each quadword becomes `P + m · q`. -/
def vredc (d t : XReg) : List Instr :=
  [xmov t d, xb .pmuludq t .xmm14, xb .pmuludq t .xmm15, xb .paddq d t]

/-- `d ← d · z · 2⁻³² mod q`, in `[0, 2q)`, with the odd doublewords of `z`
in the even doublewords of `zo`, and temporaries `t` and `u`. -/
def vmont (d z zo t u : XReg) : List Instr :=
  [.xop (.pshufd u d 0xF5), xb .pmuludq d z, xb .pmuludq u zo] ++ vredc d t ++
    [.xop (.shift .psrlq d 32)] ++ vredc u t ++ [xb .por d u]

/-- `d ← d + q` for the negative doublewords of `d`, with a temporary `t`. -/
def vcadd (d t : XReg) : List Instr :=
  [xmov t d, .xop (.shift .psrad t 31), xb .pand t .xmm15, xb .paddd d t]

/-- `d ← d mod q` for doublewords in `[0, 2q)`, with a temporary `t`. -/
def vcsub (d t : XReg) : List Instr := xb .psubd d .xmm15 :: vcadd d t

/-- The butterflies of Algorithm 41 on the doublewords of `xmm0` (`w[j]`)
and `xmm1` (`w[j + len]`) with the zetas `ζ · 2³² mod q` in `xmm13` (and
its odd doublewords in the even ones of `xmm12`): `xmm0 ← xmm0 + ζ · xmm1`
and `xmm3 ← xmm0 - ζ · xmm1`. -/
def vbfly : List Instr :=
  vmont .xmm1 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm1 .xmm2 ++
    (xmov .xmm3 .xmm0 :: xb .paddd .xmm0 .xmm1 :: vcsub .xmm0 .xmm2) ++
    (xb .psubd .xmm3 .xmm1 :: vcadd .xmm3 .xmm2)

/-- The butterflies of Algorithm 42 on the doublewords of `xmm0` (`w[j]`)
and `xmm1` (`w[j + len]`) with the zetas `ζ · 2³² mod q` in `xmm13` (and
`xmm12`): `xmm0 ← xmm0 + xmm1` and `xmm3 ← ζ · (xmm1 - xmm0)` (Algorithm
42 multiplies `w[j] - w[j + len]` by `-ζ`), from `xmm1 - xmm0 + q`. -/
def vibfly : List Instr :=
  (xmov .xmm3 .xmm1 :: xb .psubd .xmm3 .xmm0 :: xb .paddd .xmm3 .xmm15 :: xb .paddd .xmm0 .xmm1 ::
    vcsub .xmm0 .xmm2) ++ vmont .xmm3 .xmm13 .xmm12 .xmm2 .xmm4 ++ vcsub .xmm3 .xmm2

/-- The `u64`s `t (2i) + 2³² · t (2i + 1)` for `i < n / 2` at `[r + 8i]`,
through `r9`. -/
def dwordTab (t : Nat → Nat) (n : Nat) (r : Reg) : List Instr :=
  (List.range (n / 2)).flatMap fun i =>
    [.movImm64 .r9 (BitVec.ofNat 64 (t (2 * i) + 2 ^ 32 * t (2 * i + 1))), .store (at_ r (8 * i)) .r9]

end VG.Impl.MlDsa.X86_64.Arith
