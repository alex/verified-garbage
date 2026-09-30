import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Common

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly`

`expandMask(seed = rdi, gamma1 = esi, a = rdx, scratch = rcx)` (see
`Common.lean` for the layout) squeezes 640 bytes of SHAKE256 of the 66 bytes
of the seed (5 blocks, which also hold the 576 bytes that `γ₁ = 2¹⁷` needs),
and unpacks the first `32c` of them, `c = 18` or `20` (`emLoop c`, chosen by a
branch on the public `γ₁`), four coefficients of `c` bits (`c/2` bytes) at a
time: coefficient `i` is `γ₁` minus the `c` bits from bit `ci`, which are the
32-bit word at byte `⌊ci/8⌋` shifted right by `ci mod 8` and masked, stored
modulo `q` (`q` added under a mask, from the borrow of the subtraction). The
word of the last coefficient reads a byte past the output, which the mask
drops. There is no branch on the data, and the addresses depend only on the
pointers and `γ₁`: it is constant time.
-/

namespace VG.Impl.MlDsa.X86_64.Sample

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

/-- Coefficient `k` of a group of 4 of `c` bits from `rsi`, to `[rdi + 4k]`. -/
def emCoef (c k : Nat) : List Instr :=
  [.mov32 .rax (.mem (at_ .rsi (c * k / 8)))] ++
    (if c * k % 8 = 0 then [] else [.shift32 .shr .rax (c * k % 8)]) ++
    [.alu32 .and .rax (.imm (BitVec.ofNat 32 (2 ^ c - 1))), .mov32 .rdx (.imm (BitVec.ofNat 32 (2 ^ (c - 1)))),
      .alu32 .sub .rdx (.reg .rax), .alu32 .sbb .rax (.reg .rax), .alu32 .and .rax (.imm qImm),
      .alu32 .add .rdx (.reg .rax), .store32 (at_ .rdi (4 * k)) .rdx]

/-- An iteration: 4 coefficients. -/
def emBody (c : Nat) : List Instr :=
  (List.range 4).flatMap (emCoef c) ++
    [.alu .add .rsi (.imm (BitVec.ofNat 32 (c / 2))), .alu .add .rdi (.imm 16), .alu .sub .rcx (.imm 1)]

/-- The 64 iterations, from the XOF output at `scratch + 840`. -/
def emLoop (c : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov .rdi (.reg .rbp)])
    (.seq (.block [.mov32 .rcx (.imm 64)]) (.loop (.block (emBody c)) .ne))

def expandMask : Prog isa :=
  .seq (.block (pro .rcx .rdx (.reg .rsi) (.imm 66)))
    (.seq (sponge 136 640)
      (.seq (.seq (.block [.alu32 .cmp .r12 (.imm 0x20000)]) (.ite .e (emLoop 18) (emLoop 20)))
        (.block epi)))

end VG.Impl.MlDsa.X86_64.Sample
