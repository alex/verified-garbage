import VerifiedGarbage.Proof.Hmac.Sha256.X86.Init
import VerifiedGarbage.Proof.Hmac.Sha256.X86.Finalize
import VerifiedGarbage.Proof.Pbkdf2.Sha256.X86
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Hmac.Generic.X86.Sha256
import VerifiedGarbage.TCB.Artifact

/-!
# SHA-256 backends on x86

A backend is registered once. The emitter applies every generic construction
to it, so adding compression acceleration also emits the corresponding SHA,
HMAC, and PBKDF2 callers.
-/
namespace VG.Proof.Sha256.X86.Variants

open VG.X86

structure StreamFn where
  api : Api
  code : Prog isa
  contract : Contract isa
  stack : Nat := 0
  verified : Verified X86.target code contract
  ofSig : ∃ pre post leak,
    contract = api.sig.contract X86.abi pre post api.writeArgs stack leak
  ofApi : api.contracts.elim True fun f => contract = f X86.abi stack
  spSafe : code.all (fun i => !isa.writesSp i) = true

structure Backend where
  cmpN : String
  cmpC : Prog isa
  cmp : Verified X86.target cmpC Proof.Sha256.compressX86
  cmpSp : NoSp cmpC
  cmpStack : stackUse cmpC = 0
  initCt : ConstantTime isa Proof.Hmac.initSha256X86.pre Proof.Hmac.initSha256X86.pub
    (Impl.Hmac.Sha256.X86.init cmpN cmpC)
  finCt : ConstantTime isa Proof.Hmac.finalizeSha256X86.pre Proof.Hmac.finalizeSha256X86.pub
    (Impl.Hmac.Sha256.X86.finalize cmpN cmpC)
  finHashSp : NoSp (Impl.Hmac.Sha256.X86.finalizeHash cmpN cmpC)
  finHashStack : stackUse (Impl.Hmac.Sha256.X86.finalizeHash cmpN cmpC) = 20
  iterCt : ConstantTime isa Proof.Pbkdf2.iterateSha256X86.pre
    Proof.Pbkdf2.iterateSha256X86.pub (Impl.Pbkdf2.Sha256.X86.iterate cmpN cmpC)
  suffix : String
  features : List String
  functions : List StreamFn
  initSp : (Impl.Hmac.Sha256.X86.init cmpN cmpC).all (fun i => !isa.writesSp i) = true
  finSp : (Impl.Hmac.Sha256.X86.finalize cmpN cmpC).all (fun i => !isa.writesSp i) = true
  iterSp : (Impl.Pbkdf2.Sha256.X86.iterate cmpN cmpC).all (fun i => !isa.writesSp i) = true
  /-- What HMAC's proofs need of the streaming code built with `cmpC`
  (`Proof/Hmac/Generic/X86/Sha256.lean`). -/
  hmac : Proof.Hmac.Generic.X86.Sha256Facts cmpN cmpC
  hmacInitSp : (Proof.Hmac.Generic.X86.sha256H cmpN cmpC suffix).initAny.all (fun i => !isa.writesSp i) = true
  hmacFinSp : (Proof.Hmac.Generic.X86.sha256H cmpN cmpC suffix).finalize.all (fun i => !isa.writesSp i) = true

end VG.Proof.Sha256.X86.Variants
