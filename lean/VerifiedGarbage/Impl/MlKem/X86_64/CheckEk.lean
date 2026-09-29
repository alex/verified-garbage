import VerifiedGarbage.Impl.MlKem.X86_64.Encode12

/-!
# ML-KEM-768 on x86-64: `vg_mlkem768_check_ek`

`checkEk(ek = rdi) -> rax` runs over the 384 groups of 3 bytes of
`ek[0 : 1152]`, with `rcx` counting down, splitting each into its two
12-bit fields as `decode12` does. `cmp field, q` sets CF exactly when the
field is less than `q`, and `adc r8, 0` counts the fields that are. The
key passes the modulus check exactly when all 768 are: `cmp r8, 768` sets CF
exactly when one is not, and `sbb rax, rax; add rax, 1` returns `1 - CF`,
without a branch. Every address and branch depends only on the pointer.
-/

namespace VG.Impl.MlKem.X86_64

open VG.X86_64

def checkEkBody : List Instr :=
  dec12Load ++ [.mov32 .rdx (.reg .rax), .alu32 .and .rax (.imm 0xfff), .shift32 .shr .rdx 12,
    .alu32 .cmp .rax (.imm qImm), .alu .adc .r8 (.imm 0), .alu32 .cmp .rdx (.imm qImm),
    .alu .adc .r8 (.imm 0), .alu .add .rdi (.imm 3), .alu .sub .rcx (.imm 1)]

def checkEk : Prog isa :=
  .seq (.block [.mov32 .r8 (.imm 0)])
    (.seq (.seq (.block [.mov32 .rcx (.imm 384)]) (.loop (.block checkEkBody) .ne))
      (.block [.alu .cmp .r8 (.imm 768), .alu .sbb .rax (.reg .rax), .alu .add .rax (.imm 1)]))

end VG.Impl.MlKem.X86_64
