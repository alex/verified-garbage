import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Common

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly`

`rejNTT(seed = rdi, a = rsi, scratch = rdx) -> eax` (see `Common.lean` for the
layout) squeezes 1008 bytes of SHAKE128 of the 34 bytes of the seed (6
blocks; the least bound of FIPS 204 Appendix C is 894 bytes, the contract's
largest 1344), which the 336 iterations of `RejNTTPoly`'s loop take 3 bytes
at a time. The loop runs 336 times, with `rsi` at the 3 bytes of the
iteration, `rdi` = `j`, the number of coefficients sampled, and `rcx`
counting down: while `j < 256`, the value of the 3 bytes (`b₀ + 2⁸ b₁ +
2¹⁶ (b₂ mod 2⁷)`, in `r8`) is stored to `a[j]` and `j` incremented if it is
less than `q`. It returns `j >> 8`: 1 if `j = 256`, and 0 otherwise.

The loop's branches and the addresses of its stores depend on the XOF
output, a function of the seed, which the contract lets it leak.
-/

namespace VG.Impl.MlDsa.X86_64.Sample

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)

/-- The value of the 3 bytes at `rsi` in `r8`, and `j < 256` in CF. -/
def rnLoad : List Instr :=
  [.movzx8 .rax (at_ .rsi 0), .movzx8 .rdx (at_ .rsi 1), .movzx8 .r8 (at_ .rsi 2), .alu32 .and .r8 (.imm 127),
    .shift32 .ror .r8 16, .shift32 .ror .rdx 24, .alu32 .add .r8 (.reg .rdx), .alu32 .add .r8 (.reg .rax),
    .alu .cmp .rdi (.imm 256)]

/-- Store `r8` to `a[j]` if it is less than `q`. -/
def rnTry : Prog isa :=
  .seq (.block [.alu32 .cmp .r8 (.imm qImm)])
    (.ite .b (.block [.store32 aJ .r8, .alu .add .rdi (.imm 1)]) (.block []))

def rnBody : Prog isa :=
  .seq (.block rnLoad) (.seq (.ite .b rnTry (.block [])) (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]))

/-- The loop, from the XOF output at `scratch + 840`. -/
def rnLoop : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)])
    (.seq (.block [.mov32 .rcx (.imm 336)]) (.loop rnBody .ne))

def rejNTT : Prog isa :=
  .seq (.block (pro .rdx .rsi (.imm 0) (.imm 34)))
    (.seq (sponge 168 1008) (.seq rnLoop (.block (retJ ++ epi))))

end VG.Impl.MlDsa.X86_64.Sample
