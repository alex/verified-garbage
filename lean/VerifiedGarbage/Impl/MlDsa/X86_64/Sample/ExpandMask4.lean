import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.ExpandMask
import VerifiedGarbage.Impl.MlKem.X86_64.Sample4

/-!
# ML-DSA on x86-64: `vg_mldsa_expand_mask_poly4` and `vg_mldsa_expand_mask_poly4_avx2`

`expandMask4(seeds = rdi, gamma1 = esi, a = rdx, scratch = rcx)` runs
`ExpandMask`'s sampling of a polynomial (`vg_mldsa_expand_mask_poly`) on four
66-byte seeds, to the four polynomials from `a`. Both keep `scratch` in
`rbx`, `seeds` in `r12`, `a` in `r13` and `γ₁` in `r14`, and save their
caller's values and `rbp`'s in `scratch[5088..5128)`. The baseline
implementation (`expandMask4`) calls `vg_mldsa_expand_mask_poly` on each
seed, with its scratch space from byte 6144 of `scratch`.

The one for AVX2 (`expandMask4Avx2`) runs the four SHAKE256 instances at
once in the four 64-bit elements of `ymm` registers, as
`vg_mlkem_sample_ntt4_avx2` runs four of SHAKE128 (`Impl/MlKem/X86_64/Sample4.lean`,
whose layout of the first 2368 bytes of `scratch` it shares: the four
states, the second buffer of the permutation and the table of the round
constants). Each seed is 66 bytes, so the padded message is one block of
136 bytes: the code zeroes the states, writes the seed's bytes, SHAKE's
suffix `0x1f` (at byte 66) and the last bit of the padding (`0x80`, at byte
135) into each, and permutes them; it then copies the first 136 bytes of
each state to its output (from byte `2368 + 680 k`), and permutes them
again, five times in all (680 bytes, which hold the 640 that `γ₁ = 2¹⁹`
needs and the 576 of `γ₁ = 2¹⁷`). It then unpacks the output of each seed
with the loop of `vg_mldsa_expand_mask_poly` (`emBody`, for `c = 18` or
`20`, chosen by a branch on the public `γ₁`).

There is no branch on data, and every address depends only on the pointers
and `γ₁`: it is constant time.
-/

namespace VG.Impl.MlDsa.X86_64.Sample.Mask4

open VG.X86_64
open VG.Impl.MlKem.X86_64 (at_)
open VG.Impl.MlKem.X86_64.Sample4 (zero4 permArgs oRc oBuf)
open VG.Impl.Sha3.X86_64.X4 (permute4 rcTable)

/-- Where the callee-saved registers are saved. -/
def oSave : Nat := 5088

/-- The scratch space of `vg_mldsa_expand_mask_poly`, in the baseline implementation. -/
def oScalar : Nat := 6144

/-- The registers saved, at `scratch + oSave + 8 k`. -/
def saved : List Reg := [.rbx, .rbp, .r12, .r13, .r14]

/-- Save the callee-saved registers, and keep the pointers and `γ₁`. -/
def pro : List Instr :=
  (List.range 5).map (fun k => .store (at_ .rcx (oSave + 8 * k)) (saved.getD k .rbx)) ++
    [.mov .rbx (.reg .rcx), .mov .r12 (.reg .rdi), .mov .r13 (.reg .rdx), .mov .r14 (.reg .rsi)]

/-- Restore the callee-saved registers (`rbx` last). -/
def epi : List Instr :=
  ((List.range 4).map fun k => .mov (saved.getD (4 - k) .rbx) (.mem (at_ .rbx (oSave + 8 * (4 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSave))]

/-- Bytes 0 to 65 of state `k`: the 66 bytes of seed `k`, as eight lanes and
two bytes. -/
def seedLanes (k : Nat) : List Instr :=
  (List.range 8).flatMap (fun i =>
    [.mov .rax (.mem (at_ .r12 (66 * k + 8 * i))), .store (at_ .rbx (32 * i + 8 * k)) .rax]) ++
  [.movzx8 .rax (at_ .r12 (66 * k + 64)), .store8 (at_ .rbx (256 + 8 * k)) .rax,
    .movzx8 .rax (at_ .r12 (66 * k + 65)), .store8 (at_ .rbx (256 + 8 * k + 1)) .rax]

/-- The padded blocks of the four seeds, XORed into the zero states: the
seeds, SHAKE's suffix at byte 66 (byte 2 of lane 8) and `0x80` at byte 135
(byte 7 of lane 16). -/
def absorb4 : List Instr :=
  zero4 ++ (List.range 4).flatMap seedLanes ++
    .mov32 .rax (.imm 0x1f) :: (List.range 4).flatMap (fun k => [.store8 (at_ .rbx (256 + 8 * k + 2)) .rax]) ++
    .mov32 .rax (.imm 0x80) :: (List.range 4).flatMap fun k => [.store8 (at_ .rbx (512 + 8 * k + 7)) .rax]

/-- The first 136 bytes of each state to block `b` of its output. -/
def extract (b : Nat) : List Instr :=
  (List.range 4).flatMap fun k => (List.range 17).flatMap fun i =>
    [.mov .rax (.mem (at_ .rbx (32 * i + 8 * k))), .store (at_ .rbx (oBuf + 680 * k + 136 * b + 8 * i)) .rax]

/-- Permute the states and squeeze block `b`. -/
def squeeze4 (b : Nat) : Prog isa :=
  .seq (.block permArgs) (.seq permute4 (.block (extract b)))

/-- The coefficients of polynomial `k` from the output of seed `k`, `c` bits each. -/
def unpack (c k : Nat) : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 680 * k))),
      .mov .rdi (.reg .r13), .alu .add .rdi (.imm (BitVec.ofNat 32 (1024 * k))), .mov32 .rcx (.imm 64)])
    (.loop (.block (emBody c)) .ne)

def unpack4 (c : Nat) : Prog isa := .seq (unpack c 0) (.seq (unpack c 1) (.seq (unpack c 2) (unpack c 3)))

/-- `vg_mldsa_expand_mask_poly4_avx2`. `vzeroupper` clears the upper halves
of the vector registers after the last permutation. -/
def expandMask4Avx2 : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (squeeze4 3) (.seq (squeeze4 4)
      (.seq (.block [.vop .vzeroupper, .alu32 .cmp .r14 (.imm 0x20000)])
        (.seq (.ite .e (unpack4 18) (unpack4 20)) (.block epi))))))))

/-- `vg_mldsa_expand_mask_poly` on seed `k`. -/
def callK (k : Nat) : Prog isa :=
  .seq (.block [.mov .rdi (.reg .r12), .alu .add .rdi (.imm (BitVec.ofNat 32 (66 * k))), .mov .rsi (.reg .r14),
      .mov .rdx (.reg .r13), .alu .add .rdx (.imm (BitVec.ofNat 32 (1024 * k))), .mov .rcx (.reg .rbx),
      .alu .add .rcx (.imm (BitVec.ofNat 32 oScalar))])
    (.call "vg_mldsa_expand_mask_poly" expandMask)

/-- `vg_mldsa_expand_mask_poly4`: `vg_mldsa_expand_mask_poly` on each seed,
with the prologue and epilogue of `vg_mldsa_expand_mask_poly4_avx2`. -/
def expandMask4 : Prog isa :=
  .seq (.block pro) (.seq (callK 0) (.seq (callK 1) (.seq (callK 2) (.seq (callK 3) (.block epi)))))

end VG.Impl.MlDsa.X86_64.Sample.Mask4
