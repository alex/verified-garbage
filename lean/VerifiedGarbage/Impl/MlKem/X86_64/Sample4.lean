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
output, and permutes them again, three times in all.

The states are then no longer needed, and the code writes over them a
table for the sampling (`tabQ`, 2048 bytes from byte 0 of `scratch`) and
the constants of the vector code (`consts`, 192 bytes from byte 2048),
which it loads into `ymm8` to `ymm13`. For each seed it runs 168
iterations of `SampleNTT`'s loop on its 504 bytes, which samples 256
coefficients but for about one seed in 120, four at a time (`vgrp`): while
fewer than 249 coefficients are sampled (`j ≤ 248`), with AVX2 code, which
computes the eight candidates `d₁`, `d₂` of the 12 bytes in the
doublewords of `ymm0` and the mask `m` of those less than `q` in `eax`
(bit `i` for candidate `i`, `vcand`), moves those to the bottom of `ymm0`
with `vpermd`, whose indices are the nibbles of entry `m` of the table,
stores the eight doublewords to `a[j..j+8)`, and adds to `j` the number
of candidates less than `q`, the entry's high doubleword (`vput`);
otherwise (`j ≥ 249`), with four iterations of the loop of
`vg_mlkem_sample_ntt` (`snBody`), which stops at 256. A value stored but
not counted lies past the coefficients sampled, and is overwritten by the
next. Only if a seed does not reach 256 coefficients does the code call
`vg_mlkem_sample_ntt` for that seed, which samples it from the start. It
returns 1 if every seed has 256 coefficients, and 0 otherwise.

The loops' branches, the addresses of their loads from the table and of
their stores, and whether the function calls `vg_mlkem_sample_ntt`,
depend on the XOF output, a function of the seeds, and on nothing else;
every other address and branch depends only on the pointers.
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

/-! ## The vector sampling -/

/-- The positions of the set bits of the byte `m`, in order. -/
def setBits (m : Nat) : List Nat := (List.range 8).filter fun i => m / 2 ^ i % 2 = 1

/-- Entry `m` of the table: the positions of the set bits of `m` in the
nibbles of the low doubleword, from nibble 0, and their number in the high
doubleword. -/
def tabEntry (m : Nat) : Nat := (setBits m).foldr (fun p acc => p + 16 * acc) 0 + 2 ^ 32 * (setBits m).length

/-- The constants of the vector code, four quadwords each, from byte
`oCst` of `scratch` (in `ymm8` to `ymm13`): the `vpshufb` mask that puts
bytes `3i, 3i+1` and `3i+1, 3i+2` of the 12 in the low half of doublewords
`2i` and `2i+1` (bytes 0 to 5 in the low lane, 6 to 11 in the high one);
the shifts of the doublewords (`0, 4, …`); `0xfff`; `q`; the `vpshufb`
mask that puts byte 3 of each doubleword in bytes 0 to 3 of the low lane
and 4 to 7 of the high one; and the shifts of the nibbles of an entry
(`0, 4, …, 28`). -/
def consts : List (BitVec 64) :=
  [0x8080020180800100, 0x8080050480800403, 0x8080080780800706, 0x80800b0a80800a09,
    0x0000000400000000, 0x0000000400000000, 0x0000000400000000, 0x0000000400000000,
    0x00000fff00000fff, 0x00000fff00000fff, 0x00000fff00000fff, 0x00000fff00000fff,
    0x00000d0100000d01, 0x00000d0100000d01, 0x00000d0100000d01, 0x00000d0100000d01,
    0x8080808080808080, 0x0f0b070380808080, 0x808080800f0b0703, 0x8080808080808080,
    0x0000000400000000, 0x0000000c00000008, 0x0000001400000010, 0x0000001c00000018]

/-- The offset of the constants in `scratch`. -/
def oCst : Nat := 2048

/-- Quadword `i` of the table and the constants, from byte 0 of `scratch`. -/
def tabQ (i : Nat) : BitVec 64 := if i < 256 then BitVec.ofNat 64 (tabEntry i) else consts.getD (i - 256) 0

/-- The table and the constants, through `rax`. -/
def tabBuild : List Instr :=
  (List.range 280).flatMap fun i => [.movImm64 .rax (tabQ i), .store (at_ .rbx (8 * i)) .rax]

/-- The constants into `ymm8` to `ymm13`. -/
def cstLoad : List Instr :=
  [.vmovdquLoad .l256 .xmm8 (at_ .rbx oCst), .vmovdquLoad .l256 .xmm9 (at_ .rbx (oCst + 32)),
    .vmovdquLoad .l256 .xmm10 (at_ .rbx (oCst + 64)), .vmovdquLoad .l256 .xmm11 (at_ .rbx (oCst + 96)),
    .vmovdquLoad .l256 .xmm12 (at_ .rbx (oCst + 128)), .vmovdquLoad .l256 .xmm13 (at_ .rbx (oCst + 160))]

/-- `[rbx + 8 rax]`: entry `rax` of the table. -/
def tabE : MemOp := { base := .rbx, index := some .rax, scale := 8 }

/-- `[rbp + 4 rdi]`: `a[j]`. -/
def aV : MemOp := { base := .rbp, index := some .rdi, scale := 4 }

/-- The eight candidates of the 12 bytes at `rsi` in `ymm0`, and their mask
in `eax`. -/
def vcand : List Instr :=
  [.vbroadcasti128 .xmm0 (at_ .rsi 0), vb .vpshufb .xmm0 .xmm0 .xmm8, .vop (.vvar .vpsrlvd .l256 .xmm0 .xmm0 .xmm9),
    vb .vpand .xmm0 .xmm0 .xmm10, vb .vpsubd .xmm1 .xmm0 .xmm11, vb .vpshufb .xmm1 .xmm1 .xmm12,
    .vpmovmskb .l256 .rax .xmm1, .shift32 .shr .rax 12]

/-- The candidates less than `q` to `a[j..]`, and `j` and `rsi` advanced. -/
def vput : List Instr :=
  [.vmovdquLoad .l128 .xmm1 tabE, .vop (.vpbroadcastd .l256 .xmm1 .xmm1),
    .vop (.vvar .vpsrlvd .l256 .xmm1 .xmm1 .xmm13), .vop (.vpermd .xmm0 .xmm1 .xmm0), .vmovdquStore .l256 aV .xmm0,
    .alu32 .add .rdi (.mem { tabE with disp := 4 }), .alu .add .rsi (.imm 12)]

/-- Four iterations of the loop: with AVX2 if `j < 249`, and otherwise with
`snBody`. -/
def vgrp : Prog isa :=
  .seq (.block [.alu .cmp .rdi (.imm 249)])
    (.ite .b (.seq (.block vcand) (.block vput)) (.seq (.block [.mov32 .rcx (.imm 4)]) (.loop snBody .ne)))

/-- Eight iterations of the loop; `r10` counts down. -/
def vbody : Prog isa := .seq vgrp (.seq vgrp (.block [.alu .sub .r10 (.imm 1)]))

/-- The setup of the loop of seed `k`. -/
def setup (k : Nat) : List Instr :=
  [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm (BitVec.ofNat 32 (oBuf + 504 * k))),
    .mov32 .rdi (.imm 0), .mov .rbp (.reg .r13), .alu .add .rbp (.imm (BitVec.ofNat 32 (1024 * k))),
    .mov32 .r10 (.imm 21)]

/-- 168 iterations of the loop on the output of seed `k`, to polynomial
`k`. `vzeroupper` then clears the upper halves of the vector registers, so
that the SSE code that runs next (the caller's, or
`vg_mlkem_sample_ntt`'s) does not pay for mixing them. -/
def parse (k : Nat) : Prog isa :=
  .seq (.block (setup k ++ cstLoad)) (.seq (.loop vbody .ne) (.seq (.block [.vop .vzeroupper]) (fallback k)))

/-- Return `r14`, and restore the callee-saved registers (`rbx` last). -/
def epi : List Instr :=
  .mov32 .rax (.reg .r14) ::
    ((List.range 4).map fun k => .mov (saved.getD (4 - k) .rbx) (.mem (at_ .rbx (oSave + 8 * (4 - k))))) ++
    [.mov .rbx (.mem (at_ .rbx oSave))]

/-- `vg_mlkem_sample_ntt4_avx2`. -/
def sampleNTT4Avx2 : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4))
    (.seq (squeeze4 0) (.seq (squeeze4 1) (.seq (squeeze4 2) (.seq (.block tabBuild)
      (.seq (parse 0) (.seq (parse 1) (.seq (parse 2) (.seq (parse 3) (.block epi)))))))))

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

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- An implementation of `vg_mlkem_sample_ntt4` to call: its symbol and its
code. The top-level functions, which call it, are emitted once for each
(`Generic/MlKemSample4/X86_64/`). -/
structure Callee4 where
  name : String
  code : Prog isa

def Callee4.scalar : Callee4 := ⟨"vg_mlkem_sample_ntt4", Sample4.sampleNTT4⟩
def Callee4.avx2 : Callee4 := ⟨"vg_mlkem_sample_ntt4_avx2", Sample4.sampleNTT4Avx2⟩

end VG.Impl.MlKem.X86_64
