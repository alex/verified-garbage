import VerifiedGarbage.Impl.Sha512.AArch64.Sha3
import VerifiedGarbage.Impl.Sha512.AArch64.Stream

namespace VG.Impl.Sha512.AArch64.Sha3

def update : Prog AArch64.isa := Stream.updateWith compress
def finalize : Prog AArch64.isa := Stream.finalizeWith compress

end VG.Impl.Sha512.AArch64.Sha3
