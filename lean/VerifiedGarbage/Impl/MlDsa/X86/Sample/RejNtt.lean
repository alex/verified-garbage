import VerifiedGarbage.Impl.MlDsa.X86.Sample.Common

/-!
# ML-DSA on x86 (32-bit): `vg_mldsa_rej_ntt_poly`

`rejNTT(seed, a, scratch) -> eax` (see `Common.lean` for the layout) squeezes
1008 bytes of SHAKE128 of the 34 bytes of the seed (6 blocks; the least
bound of FIPS 204 Appendix C is 894 bytes, the contract's largest 1344),
which the 336 iterations of `RejNTTPoly`'s loop take 3 bytes at a time. The
loop keeps `esi` at the 3 bytes of the iteration, `edi` at the next
coefficient of `a`, `ecx` = `j`, the number of coefficients sampled, and
`ebp` = the iterations left: while `j < 256`, the value of the 3 bytes
(`b₀ + 2⁸ b₁ + 2¹⁶ (b₂ mod 2⁷)`, in `eax`) is stored to `a[j]` and `j`
incremented if it is less than `q`. It returns `j >> 8`: 1 if `j = 256`, and
0 otherwise.

The loop's branches and the addresses of its stores depend on the XOF
output, a function of the seed, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.X86.Sample

open VG.X86
open VG.Impl.MlKem.X86 (at_ leaf)

/-- The value of the 3 bytes at `esi` in `eax`, and `j < 256` in CF. -/
def rnLoad : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .edx (at_ .esi 1), .shift .ror .edx 24, .alu .add .eax (.reg .edx),
    .movzx8 .edx (at_ .esi 2), .alu .and .edx (.imm 127), .shift .ror .edx 16, .alu .add .eax (.reg .edx),
    .alu .cmp .ecx (.imm 256)]

/-- Store `eax` to `a[j]` if it is less than `q`. -/
def rnTry : Prog isa :=
  .seq (.block [.alu .cmp .eax (.imm qImm)])
    (.ite .b (.block [.store (at_ .edi 0) .eax, .alu .add .edi (.imm 4), .alu .add .ecx (.imm 1)]) (.block []))

def rnBody : Prog isa :=
  .seq (.block rnLoad) (.seq (.ite .b rnTry (.block [])) (.block [.alu .add .esi (.imm 3), .alu .sub .ebp (.imm 1)]))

/-- `esi` at the XOF output, `edi = a`, `ecx = 0`, `ebp = 336`. -/
def rnInit : List Instr :=
  [.alu .add .esi (.imm (BitVec.ofNat 32 outOff)), .mov .edi (.mem (argOp 1)), .mov .ecx (.imm 0),
    .mov .ebp (.imm 336)]

def rejNTT : Prog isa :=
  leaf <|
  .seq (sponge 2 168 (.imm 34) 1008) <|
  .seq (.block rnInit) <|
  .seq (.loop rnBody .ne) (.block (retJ .ecx))

end VG.Impl.MlDsa.X86.Sample
