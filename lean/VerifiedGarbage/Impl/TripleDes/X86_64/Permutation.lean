import VerifiedGarbage.Impl.TripleDes.X86_64.Common

namespace VG.Impl.TripleDes.X86_64

open VG.X86_64

def initialPermutation : Prog isa := .block (permuteCode Spec.TripleDes.ip 64 .rbx .rax .rbp)
def finalPermutation : Prog isa := .block (permuteCode Spec.TripleDes.fp 64 .rbx .rax .rbp)
def keyPermutation1 : Prog isa := .block (permuteCode Spec.TripleDes.pc1 64 .rbx .rax .rbp)
def keyPermutation2 : Prog isa := .block (permuteCode Spec.TripleDes.pc2 56 .rbx .rax .rbp)

end VG.Impl.TripleDes.X86_64
