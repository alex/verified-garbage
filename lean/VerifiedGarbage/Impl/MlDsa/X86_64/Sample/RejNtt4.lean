import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.RejNtt
import VerifiedGarbage.Impl.MlKem.X86_64.Sample4

/-!
# ML-DSA on x86-64: `vg_mldsa_rej_ntt_poly4` and `vg_mldsa_rej_ntt_poly4_avx2`

`rejNTT4(seeds = rdi, a = rsi, scratch = rdx) -> eax` runs `RejNTTPoly` on
four seeds. The baseline implementation (`rejNTT4`) calls
`vg_mldsa_rej_ntt_poly` on each, with the prologue and epilogue of
`vg_mlkem_sample_ntt4` (`Impl/MlKem/X86_64/Sample4.lean`: `scratch` in
`rbx`, `seeds` in `r12`, `a` in `r13`, the AND of the results in `r14`, and
their caller's values and `rbp`'s saved in `scratch[4384..4424)`) and its
scratch space from byte 6144 of `scratch`.

The one for AVX2 (`rejNTT4Avx2`) runs the four SHAKE128 instances at once
in the four 64-bit elements of `ymm` registers, as `vg_mlkem_sample_ntt4_avx2`
does, with the same code to absorb the seeds and squeeze three blocks of
each (504 bytes, from byte `2368 + 504 k` of `scratch`). It samples from them
with the loop of `vg_mldsa_rej_ntt_poly` (`rnBody`, 168 iterations of 3
bytes), keeping the number `j` of coefficients of seed `k` at
`scratch[4424 + 8 k]`; squeezes three more blocks of each to the same
place, and runs 168 more iterations of the loop on them. That is the loop of
`vg_mldsa_rej_ntt_poly` on the same 1008 bytes of output, so seed `k` has
256 coefficients if and only if `vg_mldsa_rej_ntt_poly` would have them
(and if not, neither has `RejNTTPoly` within the least bound of FIPS 204
Appendix C, 894 bytes). It returns 1 if every seed has 256 coefficients
(the AND of `j >> 8`), and 0 otherwise.

The loops' branches and the addresses of their stores depend on the XOF
output, a function of the seeds, and on nothing else; every other address
and branch depends only on the pointers.
-/

namespace VG.Impl.MlDsa.X86_64.Sample.Rej4

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Impl.MlKem.X86_64.Sample4 (absorb4 squeeze4 oRc oBuf oScalar)
open VG.Impl.Sha3.X86_64.X4 (rcTable)

/-- Where `j` of seed `k` is kept, at `scratch + oJ + 8 k`. -/
def oJ : Nat := 4424

/-- `j ← 0` for each seed. -/
def zeroJ : List Instr :=
  .mov32 .rax (.imm 0) :: (List.range 4).map fun k => .store (at_ .rbx (oJ + 8 * k)) .rax

/-- 168 iterations of `RejNTTPoly`'s loop on the 504 bytes of the output of
seed `k`, to polynomial `k`, from `j` at `scratch + oJ + 8 k`. -/
def half (k : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k))),
      .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * k))),
      .mov .rdi (.mem (at_ .rbx (oJ + 8 * k))), .mov32 .rcx (.imm 168)])
    (.loop rnBody .ne)

/-- The first half of seed `k`, and `j` kept. -/
def first (k : Nat) : Prog isa := .seq (half k) (.block [.store (at_ .rbx (oJ + 8 * k)) .rdi])

/-- The second half of seed `k`, and `r14 ← r14 ∧ (j >> 8)`. -/
def second (k : Nat) : Prog isa :=
  .seq (half k) (.block [.mov .rax (.reg .rdi), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)])

/-- `vg_mldsa_rej_ntt_poly4_avx2`. `vzeroupper` clears the upper halves of
the vector registers after the last permutation. -/
def rejNTT4Avx2 : Prog isa :=
  .seq (.block (VG.Impl.MlKem.X86_64.Sample4.pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block zeroJ)
      (.seq (first 0) (.seq (first 1) (.seq (first 2) (.seq (first 3)
        (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block [.vop .vzeroupper])
          (.seq (second 0) (.seq (second 1) (.seq (second 2) (.seq (second 3) (.block VG.Impl.MlKem.X86_64.Sample4.epi)))))))))))))))))

/-- `vg_mldsa_rej_ntt_poly` on seed `k`, and `r14 ← r14 ∧ result`. -/
def callK (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * k))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * k))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))])
    (.seq (.call "vg_mldsa_rej_ntt_poly" rejNTT) (.block [.alu32 .and .r14 (.reg .rax)]))

/-- `vg_mldsa_rej_ntt_poly4`: `vg_mldsa_rej_ntt_poly` on each seed, with the
prologue and epilogue of `vg_mldsa_rej_ntt_poly4_avx2`. -/
def rejNTT4 : Prog isa :=
  .seq (.block VG.Impl.MlKem.X86_64.Sample4.pro) (.seq (callK 0) (.seq (callK 1) (.seq (callK 2) (.seq (callK 3)
    (.block VG.Impl.MlKem.X86_64.Sample4.epi)))))

end VG.Impl.MlDsa.X86_64.Sample.Rej4
