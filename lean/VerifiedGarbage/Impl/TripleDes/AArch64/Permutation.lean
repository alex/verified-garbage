import VerifiedGarbage.Impl.TripleDes.AArch64.Common

namespace VG.Impl.TripleDes.AArch64

open VG.AArch64

def initialPermutation : Prog isa := .block (permuteCode Spec.TripleDes.ip 64 .x10 .x3 .x11 .x12)
def finalPermutation : Prog isa := .block (permuteCode Spec.TripleDes.fp 64 .x10 .x3 .x11 .x12)
def keyPermutation1 : Prog isa := .block (permuteCode Spec.TripleDes.pc1 64 .x5 .x4 .x6 .x7)
def keyPermutation2 : Prog isa := .block (permuteCode Spec.TripleDes.pc2 56 .x5 .x4 .x6 .x7)

end VG.Impl.TripleDes.AArch64
