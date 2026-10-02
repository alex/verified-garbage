import VerifiedGarbage.Impl.TripleDes.Arm.Common
namespace VG.Impl.TripleDes.Arm
open VG.Arm

def initialPermutation : Prog isa := .block (permuteCode Spec.TripleDes.ip 64 32 32 .r11 .r10 .r5 .r4 .r12 .r9)
def finalPermutation : Prog isa := .block (permuteCode Spec.TripleDes.fp 64 32 32 .r5 .r4 .r11 .r10 .r12 .r9)
def keyPermutation1 : Prog isa := .block (permuteCode Spec.TripleDes.pc1 64 32 28 .r11 .r10 .r5 .r4 .r12 .lr)
def keyPermutation2 : Prog isa := .block (permuteCode Spec.TripleDes.pc2 56 28 32 .r4 .r5 .r11 .r10 .r12 .lr)
end VG.Impl.TripleDes.Arm
