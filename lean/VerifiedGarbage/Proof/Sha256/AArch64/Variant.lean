import VerifiedGarbage.Proof.Sha256.AArch64.Stream.Md

/-!
# SHA-256 compression backends on AArch64

Each backend supplies its verified compression code and the mechanically
checked constant-time, register and frame facts for the generic streaming
wrappers. The functional streaming proofs are shared by every backend.
HMAC and PBKDF2 consume the resulting streaming functions through `MdHash`.
-/

namespace VG.Proof.Sha256.AArch64

open VG.AArch64 VG.Proof.MdStream.AArch64
open VG.Impl.MdStream.AArch64

structure Compress where
  name : String
  code : Prog isa
  verified : Verified AArch64.target code Proof.Sha256.compressAArch64
  noFrames : code.noFrames = true
  /-- Current streaming wrappers require untouched callee-saved SIMD registers. -/
  keepsV : code.allInstrs keepsV = true
  suffix : String
  features : List String
  updateCT : ConstantTime isa (updK (P := Stream.params) md).pre
    (updK (P := Stream.params) md).pub (update Stream.params name code)
  finalizeCT : ConstantTime isa (finK (P := Stream.params) md).pre
    (finK (P := Stream.params) md).pub (finalize Stream.params name code)
  updateKeeps : ((instrs (updateMain Stream.params name code)).all fun i =>
    untouched.all fun r => dstOf i != some r) = true
  finalizeKeeps : ((instrs (finalizeMain Stream.params name code)).all fun i =>
    untouched.all fun r => dstOf i != some r) = true
  updateDepth : (updateMain Stream.params name code).aarch64Depth = 0
  finalizeDepth : (finalizeMain Stream.params name code).aarch64Depth = 0

namespace Compress

variable (v : Compress)

def update : Prog isa := Impl.MdStream.AArch64.update Stream.params v.name v.code
def finalize : Prog isa := Impl.MdStream.AArch64.finalize Stream.params v.name v.code

theorem callee : CalleeOk (P := Stream.params) md v.code := ⟨v.verified.1, v.noFrames, v.keepsV⟩

theorem update_verified : Verified AArch64.target v.update Proof.Sha256.updateAArch64 := by
  have h := MdStream.AArch64.Update.verified Stream.dims v.callee v.updateCT v.updateKeeps
    (by rw [v.updateDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr hc,
    fun _ _ _ _ h => h, h.2.2⟩

theorem finalize_verified : Verified AArch64.target v.finalize Proof.Sha256.finalizeAArch64 := by
  have h := MdStream.AArch64.Finalize.verified Stream.dims Stream.shape v.callee v.finalizeCT
    v.finalizeKeeps (by rw [v.finalizeDepth]; decide)
  exact h.of_implies ⟨fun _ h => h, fun _ _ _ h iv m hr hc => h iv m hr trivial hc,
    fun _ _ _ _ h => h, h.2.2⟩

end Compress
end VG.Proof.Sha256.AArch64
