import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.CT
import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Sat
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/-! Complete signing satisfies the reviewed cached-key signing contract. -/
namespace VG.Proof.Ed25519.X86_64.SignCached

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce scalarBase_precomputed scalarMulAdd callWith)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Sha512.X86_64 (Compress)

theorem implies : signLocal.Implies (Spec.Ed25519.signCachedContract X86_64.abi 264) where
  pre := by
    sig_implies_pre [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, signLocal]
  post := by
    sig_implies_post [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, signLocal]
  pub := by
    sig_implies_pub [Spec.Ed25519.signCachedContract, Spec.Ed25519.signCachedSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, signLocal]
  sat := sat

theorem verified (v : Compress) : Verified X86_64.target (code fld fs v.callee v.suffix)
    (Spec.Ed25519.signCachedContract X86_64.abi 264) :=
  Verified.of_correct (fun _ h => sign_ok v h) (sign_ct v) implies

theorem spSafe (v : Compress) : (code fld fs v.callee v.suffix).all (fun i => !isa.writesSp i) = true := by
  have hu := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe
  have hf := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe
  have hr : scalarReduce.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have hb : (scalarBase_precomputed fld).all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by fld_lit_decide)
  have hm : scalarMulAdd.all (fun i => !isa.writesSp i) = true := Code.all_of_allInstrs (by lit_decide)
  have hi : (Impl.Sha512.X86_64.Stream.init Spec.Sha512.H0_512).all (fun i => !isa.writesSp i) = true := by
    decide +kernel
  simp only [code, body, hashSeed, hashNonce, hashChallenge, init, update, finalize, reduce, callWith,
    Code.all, hu, hf, hr, hb, hm, hi, Bool.and_true]
  decide

end VG.Proof.Ed25519.X86_64.SignCached
