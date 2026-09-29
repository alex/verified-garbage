import VerifiedGarbage.Impl.MlKem.X86_64.CheckEk

/-!
# ML-KEM-1024 on x86-64: `vg_mlkem1024_check_ek`

`checkEk1024(ek = rdi) -> rax` is `vg_mlkem768_check_ek`
(`Impl/MlKem/X86_64/CheckEk.lean`) for the 512 groups of 3 bytes of
`ek[0 : 1536]`: it counts the 1024 fields less than `q` in `r8` and returns
1 exactly when all are, without a branch. Every address and branch depends
only on the pointer.
-/

namespace VG.Impl.MlKem1024.X86_64

open VG.X86_64 VG.Impl.MlKem.X86_64

def checkEk1024 : Prog isa :=
  .seq (.block [.mov32 .r8 (.imm 0)])
    (.seq (.seq (.block [.mov32 .rcx (.imm 512)]) (.loop (.block checkEkBody) .ne))
      (.block [.alu .cmp .r8 (.imm 1024), .alu .sbb .rax (.reg .rax), .alu .add .rax (.imm 1)]))

end VG.Impl.MlKem1024.X86_64
