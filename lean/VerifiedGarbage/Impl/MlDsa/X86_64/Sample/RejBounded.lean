import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Common

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_bounded_poly`

`rejBounded(seed = rdi, eta = esi, a = rdx, scratch = rcx) -> eax` (see
`Common.lean` for the layout) squeezes 544 bytes of SHAKE256 of the 66 bytes
of the seed (4 blocks; the least bound of FIPS 204 Appendix C is 481 bytes,
the contract's largest 1088), which the 544 iterations of
`RejBoundedPoly`'s loop take a byte at a time. The loop (`rbLoop η`, one for
each `η`, chosen by a branch on the public `η`) runs 544 times, with `rsi` at
the byte of the iteration, `rdi` = `j`, the number of coefficients sampled,
and `rcx` counting down: while `j < 256`, each half-byte `b` of the byte (low
first, in `rdx`) that `CoeffFromHalfByte` accepts (`b < 15` for `η = 2`,
`b < 9` for `η = 4`) gives the coefficient `η - (b mod 5)` or `η - b`,
stored modulo `q` to `a[j]` (and `j` incremented; the high half-byte only if
`j < 256` still). It returns `j >> 8`: 1 if `j = 256`, and 0 otherwise.

The coefficient is computed without a branch or a table (`rbVal`): `b mod 5`
by subtracting 10 and then 5 where they are no greater, `sub` setting CF when
they are greater and `sbb` making it a mask, and `q` added under a mask to
`η - (b mod 5)` if it is negative. So the loop's branches and the addresses
of its stores depend only on which half-bytes are accepted (and `j`, which
counts them), which the contract lets it leak, not on the coefficients.
-/

namespace VG.Impl.MlDsa.X86_64.Sample

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

/-- `rdx ← rdx - s` if `s ≤ rdx`, with `r8` as a mask. -/
def csub (s : BitVec 32) : List Instr :=
  [.alu32 .sub .rdx (.imm s), .alu32 .sbb .r8 (.reg .r8), .alu32 .and .r8 (.imm s), .alu32 .add .rdx (.reg .r8)]

/-- `r8 ← (η - rdx) mod q`, for `rdx ≤ q + η`, with `rdx` as a mask. -/
def etaSub (η : BitVec 32) : List Instr :=
  [.mov32 .r8 (.imm η), .alu32 .sub .r8 (.reg .rdx), .alu32 .sbb .rdx (.reg .rdx), .alu32 .and .rdx (.imm qImm),
    .alu32 .add .r8 (.reg .rdx)]

/-- The coefficient of an accepted half-byte `rdx`, modulo `q`, in `r8`:
`η - (b mod 5)` for `η = 2`, `η - b` for `η = 4`. -/
def rbVal : Nat → List Instr
  | 2 => csub 10 ++ csub 5 ++ etaSub 2
  | _ => etaSub 4

/-- The half-bytes `CoeffFromHalfByte` accepts: those less than this. -/
def rbBound : Nat → BitVec 32
  | 2 => 15
  | _ => 9

/-- Store the coefficient of the half-byte `rdx` to `a[j]` if it is accepted. -/
def rbTry (η : Nat) : Prog isa :=
  .seq (.block [.alu32 .cmp .rdx (.imm (rbBound η))])
    (.ite .b (.block (rbVal η ++ [.store32 aJ .r8, .alu .add .rdi (.imm 1)])) (.block []))

/-- The byte at `rsi` in `rax`, its low half-byte in `rdx`, and `j < 256` in CF. -/
def rbLoad : List Instr :=
  [.movzx8 .rax (at_ .rsi 0), .mov32 .rdx (.reg .rax), .alu32 .and .rdx (.imm 15), .alu .cmp .rdi (.imm 256)]

/-- The high half-byte in `rdx`, and `j < 256` in CF. -/
def rbHi : List Instr := [.shift32 .shr .rax 4, .mov32 .rdx (.reg .rax), .alu .cmp .rdi (.imm 256)]

def rbBody (η : Nat) : Prog isa :=
  .seq (.block rbLoad)
    (.seq (.ite .b (.seq (rbTry η) (.seq (.block rbHi) (.ite .b (rbTry η) (.block [])))) (.block []))
      (.block [.alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]))

/-- The loop, from the XOF output at `scratch + 840`. -/
def rbLoop (η : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)])
    (.seq (.block [.mov32 .rcx (.imm 544)]) (.loop (rbBody η) .ne))

def rejBounded : Prog isa :=
  .seq (.block (pro .rcx .rdx (.reg .rsi) (.imm 66)))
    (.seq (sponge 136 544)
      (.seq (.seq (.block [.alu32 .cmp .r12 (.imm 2)]) (.ite .e (rbLoop 2) (rbLoop 4)))
        (.block (retJ ++ epi))))

end VG.Impl.MlDsa.X86_64.Sample
