import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Derive.CT
import VerifiedGarbage.Proof.Hmac.X86_64.Shared
import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC-SHA-256 on X86_64: the shared contract

Untrusted: everything here is checked by Lean. The proof is written against
a per-target contract (`Proof/Pbkdf2/X86_64/Contract.lean`); this theorem
moves it to the shared contract of `Spec/Pbkdf2/Contract.lean`, which the
artifact is emitted with. They hold for any implementation `f` of the
compression function.
-/

namespace VG.Proof.Pbkdf2.X86_64.Shared

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem iterate {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Pbkdf2.X86_64.iterate f)
      (Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8) :=
  (Proof.Pbkdf2.X86_64.Iterate.verified_of hf (by
    simp only [Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
      Impl.Pbkdf2.X86_64.compressBlock, Code.allInstrs, hm, Bool.and_true]
    decide +kernel) (Proof.Pbkdf2.X86_64.Iterate.constantTime hf)).of_implies (by
    contract_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig,
      Proof.Pbkdf2.iterateSha256X86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Pbkdf2.X86_64.Iterate.sat] using Proof.Pbkdf2.X86_64.Iterate.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem iterate_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Pbkdf2.X86_64.iterate f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Code.all, h, Bool.and_true]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- The whole of PBKDF2-HMAC-SHA-256, calling the functions made with any
compression function `f`, whose names end with `sfx`. -/
theorem derive {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) (sfx : String) :
    Verified X86_64.target (Impl.Pbkdf2.X86_64.derive f sfx)
      (Spec.Pbkdf2.pbkdf2Sha256Contract X86_64.abi 24) :=
  (Proof.Pbkdf2.X86_64.Derive.verified_of ⟨hf, hm⟩ sfx).of_implies (by
    contract_implies [Spec.Pbkdf2.pbkdf2Sha256Contract, Spec.Pbkdf2.pbkdf2Sha256Sig,
      Proof.Pbkdf2.pbkdf2Sha256X86_64, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
      [Proof.Pbkdf2.X86_64.Derive.sat, X86_64.stackArg, X86_64.stackArgAddr, Mem.readW, Mem.read]
      using Proof.Pbkdf2.X86_64.Derive.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem derive_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true)
    (sfx : String) :
    (Impl.Pbkdf2.X86_64.derive f sfx).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Pbkdf2.X86_64.derive, Impl.Pbkdf2.X86_64.hashKey, Impl.Pbkdf2.X86_64.keySalt,
    Impl.Pbkdf2.X86_64.block, Impl.Pbkdf2.X86_64.blockU, Impl.Pbkdf2.X86_64.blockT,
    Impl.Pbkdf2.X86_64.blockOut, Impl.Pbkdf2.X86_64.byteLoop, Code.all,
    Proof.Sha256.X86_64.Shared.update_spSafe h, Proof.Sha256.X86_64.Shared.finalize_spSafe h,
    Proof.Hmac.X86_64.Shared.init_spSafe h, Proof.Hmac.X86_64.Shared.finalize_spSafe h,
    iterate_spSafe h, Bool.and_true, Bool.true_and]
  decide +kernel

end VG.Proof.Pbkdf2.X86_64.Shared
