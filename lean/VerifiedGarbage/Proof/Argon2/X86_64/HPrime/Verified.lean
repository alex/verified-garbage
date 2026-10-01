import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.CT

/-! # Verified H′ for any x86-64 BLAKE2b backend -/

namespace VG.Proof.Argon2.X86_64.HPrime

open VG VG.X86_64 VG.Impl.Argon2.X86_64.HPrime

theorem verified (v : Proof.Blake2.X86_64.Backend) :
    Verified X86_64.target (code (hash v)) (Spec.Argon2.hPrimeContract X86_64.abi 16) :=
  Verified.of_correct (code_correct v) (code_ct v) contract_implies

theorem spSafe (v : Proof.Blake2.X86_64.Backend) : (code (hash v)).all (fun i => !isa.writesSp i) = true := by
  have init : (hash v).init.all (fun i => !isa.writesSp i) = true := by
    apply Code.all_of_allInstrs
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (hash v).update.all (fun i => !isa.writesSp i) = true := v.updateSpSafe
  have finalize : (hash v).finalize.all (fun i => !isa.writesSp i) = true := v.finalizeSpSafe
  simp only [code, setup, saved, first, chooseLength, Impl.Argon2.X86_64.HPrime.init,
    initArgs, absorbFixed, fixedArgs, Impl.Argon2.X86_64.HPrime.update, updateArgs,
    absorbInput, inputArgs, finishInput, Impl.Argon2.X86_64.HPrime.finalize, finalizeArgs,
    finishOutput, extendDigest, emitPrefix, copy, copyByte, chain, next, copyRemaining,
    restore, Code.all]
  rw [init, update, finalize]
  decide +kernel

end VG.Proof.Argon2.X86_64.HPrime
