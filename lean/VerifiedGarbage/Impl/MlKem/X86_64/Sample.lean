import VerifiedGarbage.Impl.MlKem.X86_64.Common
import VerifiedGarbage.Impl.Sha3.X86_64.Stream

/-!
# ML-KEM on x86-64: `vg_mlkem_sample_ntt`

`sampleNTT(seed = rdi, a = rsi, scratch = rdx) -> eax` keeps `scratch` in
`rbx` and `a` in `rbp`, whose caller's values it saves in
`scratch[1680..1696)` (the functions it calls preserve them). `scratch`
holds, from byte 0, the Keccak state (200 bytes), the working space of the
sponge functions (640 bytes), and the 840 bytes of XOF output.

It zeroes the state (the empty message), absorbs the 34 bytes of the seed
with `vg_keccak_absorb` (rate 168), pads it with `vg_keccak_pad` (SHAKE's
suffix `0x1f`), and squeezes 840 bytes with `vg_keccak_squeeze`: the first
280 iterations of `SampleNTT`'s loop take 3 bytes each. Then the loop runs
280 times, with `rsi` at the 3 bytes of the iteration, `rdi` = `j`, the
number of coefficients sampled, and `rcx` counting down: while `j < 256`,
each of the two 12-bit values `d₁`, `d₂` of the 3 bytes (in `r9` and `r8`)
that is less than `q` is stored to `a[j]` (at `rbp + 4 rdi`), and `j`
incremented (`d₂` only if `j < 256` still). It returns `j >> 8`: 1 if
`j = 256`, and 0 otherwise.

The loop's branches and the addresses of its stores depend on the XOF
output, a function of the seed, and on nothing else; every other address
and branch depends only on the pointers.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

/-- `a[j]`: `[rbp + 4 rdi]`. -/
def aJ : MemOp := { base := .rbp, index := some .rdi, scale := 4 }

/-- The 25 lanes of the state at `b + off`, zeroed (with `rax` = 0). -/
def zeroSt (b : Reg) (off : Nat) : List Instr := (List.range 25).flatMap fun i => [.store (at_ b (off + 8 * i)) .rax]

/-- Save `rbx`, `rbp`, keep the pointers, zero the state, and the arguments of `absorb`. -/
def snPro : List Instr :=
  [.store (at_ .rdx 1680) .rbx, .store (at_ .rdx 1688) .rbp, .mov .rbx (.reg .rdx), .mov .rbp (.reg .rsi),
    .mov .rcx (.reg .rdi), .mov32 .rax (.imm 0)] ++ zeroSt .rbx 0 ++
    [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 168), .mov32 .rdx (.imm 0), .mov32 .r8 (.imm 34),
      .mov .r9 (.reg .rbx), .alu .add .r9 (.imm 200)]

/-- The arguments of `pad`. -/
def snPadArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 168), .mov32 .rdx (.imm 34), .mov32 .rcx (.imm 0x1f),
    .mov .r8 (.reg .rbx), .alu .add .r8 (.imm 200)]

/-- The arguments of `squeeze`. -/
def snSqzArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov32 .rsi (.imm 168), .mov32 .rdx (.imm 0), .mov .rcx (.reg .rbx),
    .alu .add .rcx (.imm 840), .mov32 .r8 (.imm 840), .mov .r9 (.reg .rbx), .alu .add .r9 (.imm 200)]

/-- The 3 bytes at `rsi`: `d₁` in `r9` and `d₂` in `r8`, and `j < 256` in CF. -/
def snLoad : List Instr :=
  [.movzx8 .rax (at_ .rsi 0), .movzx8 .rdx (at_ .rsi 1), .movzx8 .r8 (at_ .rsi 2), .mov32 .r9 (.reg .rdx),
    .alu32 .and .r9 (.imm 15), .shift32 .ror .r9 24, .alu32 .add .r9 (.reg .rax), .shift32 .shr .rdx 4,
    .shift32 .ror .r8 28, .alu32 .add .r8 (.reg .rdx), .alu .cmp .rdi (.imm 256)]

/-- Store the value in `r` to `a[j]` if it is less than `q`. -/
def snTry (r : Reg) : Prog isa :=
  .seq (.block [.alu32 .cmp r (.imm qImm)])
    (.ite .b (.block [.store32 aJ r, .alu .add .rdi (.imm 1)]) (.block []))

def snBody : Prog isa :=
  .seq (.block snLoad)
    (.seq (.ite .b (.seq (snTry .r9) (.seq (.block [.alu .cmp .rdi (.imm 256)]) (.ite .b (snTry .r8) (.block []))))
        (.block []))
      (.block [.alu .add .rsi (.imm 3), .alu .sub .rcx (.imm 1)]))

/-- The loop, from the XOF output at `scratch + 840`. -/
def snLoop : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rbx), .alu .add .rsi (.imm 840), .mov32 .rdi (.imm 0)])
    (.seq (.block [.mov32 .rcx (.imm 280)]) (.loop snBody .ne))

/-- The return value, and `rbx`, `rbp` restored. -/
def snEpi : List Instr :=
  [.mov .rax (.reg .rdi), .shift .shr .rax 8, .mov .rbp (.mem (at_ .rbx 1688)), .mov .rbx (.mem (at_ .rbx 1680))]

def sampleNTT : Prog isa :=
  .seq (.block snPro)
    (.seq (.call "vg_keccak_absorb" Impl.Sha3.X86_64.Stream.absorb)
      (.seq (.block snPadArgs)
        (.seq (.call "vg_keccak_pad" Impl.Sha3.X86_64.Stream.pad)
          (.seq (.block snSqzArgs)
            (.seq (.call "vg_keccak_squeeze" Impl.Sha3.X86_64.Stream.squeeze)
              (.seq snLoop (.block snEpi)))))))

end VG.Impl.MlKem.X86_64
