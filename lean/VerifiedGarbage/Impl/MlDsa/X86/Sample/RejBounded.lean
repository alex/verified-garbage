import VerifiedGarbage.Impl.MlDsa.X86.Sample.Common

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_rej_bounded_poly`

`rejBounded(seed, eta, a, scratch) -> eax` (see `Common.lean` for the
layout) squeezes 544 bytes of SHAKE256 of the 66 bytes of the seed (4
blocks; the least bound of FIPS 204 Appendix C is 481 bytes, the contract's
largest 1088), which the 544 iterations of `RejBoundedPoly`'s loop take a
byte at a time. The loop (`rbLoop η`, one for each `η`, chosen by a branch
on the public `η`) keeps `esi` at the byte of the iteration, `edi` at the
next coefficient of `a`, `ecx` = `j`, the number of coefficients sampled,
and `ebp` counting down: while `j < 256`, each half-byte `b` of the byte
(low first, in `edx`; the byte is in `eax`) that `CoeffFromHalfByte`
accepts (`b < 15` for `η = 2`, `b < 9` for `η = 4`) gives the coefficient
`η - (b mod 5)` or `η - b`, stored modulo `q` to `a[j]` (and `j`
incremented; the high half-byte only if `j < 256` still). It returns
`j >> 8`: 1 if `j = 256`, and 0 otherwise.

The coefficient is computed without a branch or a table (`rbVal`), in
`ebx`: `b mod 5` by subtracting 10 and then 5 where they are no greater,
`sub` setting CF when they are greater and `sbb` making it a mask, and `q`
added under a mask to `η - (b mod 5)` if it is negative. So the loop's
branches and the addresses of its stores depend only on which half-bytes
are accepted (and `j`, which counts them), which the contract lets it leak,
not on the coefficients.
-/

namespace VG.Impl.MlDsa.X86.Sample

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-- `edx ← edx - s` if `s ≤ edx`, with `ebx` as a mask. -/
def csub (s : BitVec 32) : List Instr :=
  [.alu .sub .edx (.imm s), .alu .sbb .ebx (.reg .ebx), .alu .and .ebx (.imm s), .alu .add .edx (.reg .ebx)]

/-- `ebx ← (η - edx) mod q`, for `edx ≤ q + η`, with `edx` as a mask. -/
def etaSub (η : BitVec 32) : List Instr :=
  [.mov .ebx (.imm η), .alu .sub .ebx (.reg .edx), .alu .sbb .edx (.reg .edx), .alu .and .edx (.imm qImm),
    .alu .add .ebx (.reg .edx)]

/-- The coefficient of an accepted half-byte `edx`, modulo `q`, in `ebx`:
`η - (b mod 5)` for `η = 2`, `η - b` for `η = 4`. -/
def rbVal : Nat → List Instr
  | 2 => csub 10 ++ csub 5 ++ etaSub 2
  | _ => etaSub 4

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → BitVec 32
  | 2 => 15
  | _ => 9

/-- Store the coefficient of the half-byte `edx` to `a[j]` if it is accepted. -/
def rbTry (η : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .edx (.imm (rbBound η))])
    (.ite .b (.block (rbVal η ++ [.store (at_ .edi 0) .ebx, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]))
      (.block []))

/-- The byte at `esi` in `eax`, its low half-byte in `edx`, and `j < 256` in CF. -/
def rbLoad : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .mov .edx (.reg .eax), .alu .and .edx (.imm 15), .alu .cmp .ecx (.imm 256)]

/-- The high half-byte in `edx`, and `j < 256` in CF. -/
def rbHi : List Instr := [.shift .shr .eax 4, .mov .edx (.reg .eax), .alu .cmp .ecx (.imm 256)]

def rbBody (η : Nat) : Prog isa :=
  .seq (.block rbLoad)
    (.seq (.ite .b (.seq (rbTry η) (.seq (.block rbHi) (.ite .b (rbTry η) (.block [])))) (.block []))
      (.block [.alu .add .esi (.imm 1), .alu .sub .ebp (.imm 1)]))

/-- The loop, from the XOF output at `esi + 840`. -/
def rbLoop (η : Nat) : Prog isa :=
  .seq (.block [.alu .add .esi (.imm (BitVec.ofNat 32 outOff)), .mov .ecx (.imm 0), .mov .ebp (.imm 544)])
    (.loop (rbBody η) .ne)

def rejBounded : Prog isa :=
  leaf <|
  .seq (sponge 3 136 (.imm 66) 544) <|
  .seq (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 2)]) <|
  .seq (.ite .e (rbLoop 2) (rbLoop 4)) (.block (retJ .ecx))

end VG.Impl.MlDsa.X86.Sample
