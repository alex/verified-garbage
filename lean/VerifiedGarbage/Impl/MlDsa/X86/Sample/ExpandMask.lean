import VerifiedGarbage.Impl.MlDsa.X86.Sample.Common

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_expand_mask_poly`

`expandMask(seed, gamma1, a, scratch)` (see `Common.lean` for the layout)
squeezes 640 bytes of SHAKE256 of the 66 bytes of the seed (5 blocks, which
also hold the 576 bytes that `γ₁ = 2¹⁷` needs), and unpacks the first `32c`
of them, `c = 18` or `20` (`emLoop c`, chosen by a branch on the public
`γ₁`), four coefficients of `c` bits (`c/2` bytes) at a time, with `esi` at
the bytes, `edi` at the coefficients and `ecx` counting down: coefficient
`i` is `γ₁` minus the `c` bits from bit `ci`, which are the 32-bit word at
byte `⌊ci/8⌋` shifted right by `ci mod 8` and masked, stored modulo `q` (`q`
added under a mask, from the borrow of the subtraction). The word of the
last coefficient reads a byte past the output, which the mask drops. There
is no branch on the data, and the addresses depend only on the pointers and
`γ₁`: it is constant time.
-/

namespace VG.Impl.MlDsa.X86.Sample

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-- Coefficient `k` of a group of 4 of `c` bits from `esi`, to `[edi + 4k]`. -/
def emCoef (c k : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .esi (c * k / 8)))] ++
    (if c * k % 8 = 0 then [] else [.shift .shr .eax (c * k % 8)]) ++
    [.alu .and .eax (.imm (BitVec.ofNat 32 (2 ^ c - 1))), .mov .edx (.imm (BitVec.ofNat 32 (2 ^ (c - 1)))),
      .alu .sub .edx (.reg .eax), .alu .sbb .eax (.reg .eax), .alu .and .eax (.imm qImm),
      .alu .add .edx (.reg .eax), .store (at_ .edi (4 * k)) .edx]

/-- An iteration: 4 coefficients. -/
def emBody (c : Nat) : List Instr :=
  (List.range 4).flatMap (emCoef c) ++
    [.alu .add .esi (.imm (BitVec.ofNat 32 (c / 2))), .alu .add .edi (.imm 16), .alu .sub .ecx (.imm 1)]

/-- The 64 iterations, from the XOF output at `esi + 840`, to `a` at `edi`. -/
def emLoop (c : Nat) : Prog isa :=
  .seq (.block [.alu .add .esi (.imm (BitVec.ofNat 32 outOff)), .mov .ecx (.imm 64)])
    (.loop (.block (emBody c)) .ne)

def expandMask : Prog isa :=
  leaf <|
  .seq (sponge 3 136 (.imm 66) 640) <|
  .seq (.block [.mov .edi (.mem (argOp 2)), .mov .eax (.mem (argOp 1)), .alu .cmp .eax (.imm 0x20000)])
    (.ite .e (emLoop 18) (emLoop 20))

end VG.Impl.MlDsa.X86.Sample
