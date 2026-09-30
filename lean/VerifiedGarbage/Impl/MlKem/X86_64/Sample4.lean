import VerifiedGarbage.Impl.MlKem.X86_64.Sample
import VerifiedGarbage.Impl.Sha3.X86_64.X4

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt4` and `vg_mlkem_sample_ntt4_avx2`

`sampleNTT4(seeds = rdi, a = rsi, scratch = rdx) -> eax` runs `SampleNTT`
on four seeds. The baseline implementation (`sampleNTT4`) calls
`vg_mlkem_sample_ntt` on each, with the prologue and epilogue below and its
scratch space from byte 6144 of `scratch`. The one for AVX2
(`sampleNTT4Avx2`) runs the four at once: the four SHAKE128 instances in the four 64-bit
elements of `ymm` registers (`Impl/Sha3/X86_64/X4.lean`). It keeps
`scratch` in `rbx`, `seeds` in `r12`, `a` in `r13` and the AND of the
results in `r14`, and saves their caller's values and `rbp`'s in
`scratch[4384..4424)`. `scratch` holds, from byte 0, the four states
(interleaved, 800 bytes), the second buffer of the permutation (800
bytes), the table of the round constants (768 bytes), the first 504 bytes
of the XOF output of each seed (from byte `2368 + 504 k`), and, from byte
6144, the scratch space of `vg_mlkem_sample_ntt` (2048 bytes).

Each seed is at most 34 bytes, so the padded message is one block: the
code zeroes the states, writes the seed's bytes, SHAKE's suffix `0x1f` (at
byte 34) and the last bit of the padding (`0x80`, at byte 167) into each,
and permutes them. It then copies the first 168 bytes of each state to its
output, and permutes them again, three times in all. For each seed it runs
168 iterations of the loop of `vg_mlkem_sample_ntt` (`snBody`) on its 504
bytes, which samples 256 coefficients but for about one seed in 120; only
if one does not does it call `vg_mlkem_sample_ntt` for that seed, which
samples it from the start. It returns 1 if every seed has 256 coefficients,
and 0 otherwise.

The loops' branches, the addresses of their stores, and whether the
function calls `vg_mlkem_sample_ntt`, depend on the XOF output, a function
of the seeds, and on nothing else; every other address and branch depends
only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64.Sample4

open VG.X86_64
open VG.Impl.MlKem.X86_64 (snBody sampleNTT)
open VG.Impl.Sha3.X86_64.X4 (vb st permute4 rcTable)

/-- The offsets in the scratch space. -/
def oTmp : Nat := 800
def oRc : Nat := 1600
def oBuf : Nat := 2368
def oSave : Nat := 4384
def oScalar : Nat := 6144

/-- The registers saved, at `scratch + oSave + 8 k`. -/
def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- Save the callee-saved registers, keep the pointers, and `r14 ← 1`. -/
def pro : List Instr :=
  (List.range 5).map (fun k => .store (at_ .rdx (oSave + 8 * k)) (saved.getD k .rbx)) ++
    [.mov .rbx (.reg .rdx), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rsi), .mov32 .r14 (.imm 1)]

/-- The four states, zeroed. -/
def zero4 : List Instr :=
  vb .vpxor .xmm0 .xmm0 .xmm0 :: (List.range 25).flatMap fun i => [st .rbx i .xmm0]

/-- Bytes 0 to 33 of state `k`: the 34 bytes of seed `k`, as four lanes and
two bytes. -/
def seedLanes (k : Nat) : List Instr :=
  (List.range 4).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (34 * k + 8 * i))), .store (at_ .rbx (32 * i + 8 * k)) .rax]) ++
  [.movzx8 .rax (at_ .r12 (34 * k + 32)), .store8 (at_ .rbx (128 + 8 * k)) .rax,
    .movzx8 .rax (at_ .r12 (34 * k + 33)), .store8 (at_ .rbx (128 + 8 * k + 1)) .rax]

/-- The padded blocks of the four seeds, XORed into the zero states: the
seeds, SHAKE's suffix at byte 34 (byte 2 of lane 4) and `0x80` at byte 167
(byte 7 of lane 20). -/
def absorb4 : List Instr :=
  zero4 ++ (List.range 4).flatMap seedLanes ++
    .mov32 .rax (.imm 0x1f) :: (List.range 4).flatMap (fun k => [.store8 (at_ .rbx (128 + 8 * k + 2)) .rax]) ++
    .mov32 .rax (.imm 0x80) :: (List.range 4).flatMap fun k => [.store8 (at_ .rbx (640 + 8 * k + 7)) .rax]

/-- The arguments of `permute4`. -/
def permArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 oTmp)),
    .mov .rdx (.reg .rbx), .alu .add .rdx (.imm (BitVec.ofNat 32 oRc)), .mov .rcx (.reg .rbx),
    .alu .add .rcx (.imm (BitVec.ofNat 32 oBuf))]

/-- The first 168 bytes of each state to block `b` of its output. -/
def extract (b : Nat) : List Instr :=
  (List.range 4).flatMap fun k => (List.range 21).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (32 * i + 8 * k))), .store (at_ .rbx (oBuf + 504 * k + 168 * b + 8 * i)) .rax]

/-- Permute the states and squeeze block `b`. -/
def squeeze4 (b : Nat) : Prog isa :=
  .seq (.block permArgs) (.seq permute4 (.block (extract b)))

/-- If seed `k` has fewer than 256 coefficients: `vg_mlkem_sample_ntt` on
it, and `r14 ← r14 ∧ result`. -/
def fallback (k : Nat) : Prog isa :=
  .seq (.block [.alu .cmp .rdi (.imm 256)])
    (.ite .b
      (.seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * k))),
          .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * k))), .mov .rdx (.reg .rbx),
          .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))])
        (.seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.alu32 .and .r14 (.reg .rax)])))
      (.block []))

/-- 168 iterations of the loop on the output of seed `k`, to polynomial `k`. -/
def parse (k : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k))),
      .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * k))),
      .mov32 .rcx (.imm 168)])
    (.seq (.loop snBody .ne) (fallback k))

/-- Return `r14`, and restore the callee-saved registers (`rbx` last). -/
def epi : List Instr :=
  .mov32 .rax (.reg .r14) ::
    ((List.range 4).map fun k => .mov (saved.getD (4 - k) .rbx) (.mem (at_ .rbx (oSave + 8 * (4 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSave))]

/-- `vg_mlkem_sample_ntt4_avx2`. -/
def sampleNTT4Avx2 : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2)
      (.seq (parse 0) (.seq (parse 1) (.seq (parse 2) (.seq (parse 3) (.block epi))))))))

/-- `vg_mlkem_sample_ntt` on seed `k`, and `r14 ← r14 ∧ result`. -/
def callK (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (34 * k))),
      .mov .rsi (.reg .r13), .alu .add .rsi (.imm (BitVec.ofNat 32 (1024 * k))), .mov .rdx (.reg .rbx),
      .alu .add .rdx (.imm (BitVec.ofNat 32 oScalar))])
    (.seq (.call "vg_mlkem_sample_ntt" sampleNTT) (.block [.alu32 .and .r14 (.reg .rax)]))

/-- `vg_mlkem_sample_ntt4`: `vg_mlkem_sample_ntt` on each seed, with the
prologue and epilogue of `vg_mlkem_sample_ntt4_avx2`. -/
def sampleNTT4 : Prog isa :=
  .seq (.block pro) (.seq (callK 0) (.seq (callK 1) (.seq (callK 2) (.seq (callK 3) (.block epi)))))

end VG.Impl.MlKem.X86_64.Sample4
