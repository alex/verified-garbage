import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Update
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Finalize

/-! Verified compression backends and their generic streaming wrappers. -/

namespace VG.Proof.Sha512.AArch64

open VG.AArch64 VG.Impl.Sha512.AArch64.Stream
open VG.Proof.Sha512.AArch64.Stream (untouched)

structure Compress where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sha512.compressAArch64
  noFrames : code.noFrames = true
  noCalls : code.noCalls = true
  keepsV : code.allInstrs VG.AArch64.keepsV = true
  suffix : String
  features : List String
  updateCT : ConstantTime isa Proof.Sha512.updateAArch64.pre Proof.Sha512.updateAArch64.pub (updateWith code)
  finalizeCT : ConstantTime isa Proof.Sha512.finalizeAArch64.pre Proof.Sha512.finalizeAArch64.pub (finalizeWith code)
  updateKeeps : ((instrs (updateWith code)).all fun i => untouched.all fun r => dstOf i != some r) = true
  finalizeKeeps : ((instrs (finalizeWith code)).all fun i => untouched.all fun r => dstOf i != some r) = true
  /-- Like the GPR certificates, current wrappers require syntactically untouched SIMD saves. -/
  updateKeepsV : (updateWith code).allInstrs VG.AArch64.keepsV = true
  finalizeKeepsV : (finalizeWith code).allInstrs VG.AArch64.keepsV = true
  updateDepth : (updateWith code).aarch64Depth = 0
  finalizeDepth : (finalizeWith code).aarch64Depth = 0

namespace Compress
variable (v : Compress)
def update : Prog isa := updateWith v.code
def finalize : Prog isa := finalizeWith v.code

theorem update_verified : Verified AArch64.target v.update Proof.Sha512.updateAArch64 :=
  Stream.Update.update_verified_of v.verified v.noCalls v.updateKeeps v.updateKeepsV v.updateCT

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sha512.finalizeAArch64 :=
  Stream.Finalize.finalize_verified_of v.verified v.noCalls v.finalizeKeeps v.finalizeKeepsV v.finalizeCT

end Compress
end VG.Proof.Sha512.AArch64
