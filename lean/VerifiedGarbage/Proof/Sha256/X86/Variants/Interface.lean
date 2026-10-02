import VerifiedGarbage.Proof.Hmac.Sha256.X86.Init
import VerifiedGarbage.Proof.Hmac.Sha256.X86.Finalize
import VerifiedGarbage.Proof.Pbkdf2.Sha256.X86
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.TCB.Artifact
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256Fns

/-!
# SHA-256 backends on x86

A backend is registered once. The emitter applies every generic construction
to it, so adding compression acceleration also emits the corresponding SHA,
HMAC, and PBKDF2 callers (PBKDF2's whole derivation among them, which calls
the streaming, HMAC and PBKDF2 functions made with the backend).
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
  /-- The streaming `update` and `finalize` calling `cmpC` (as in
  `functions`), which PBKDF2's whole derivation calls, verified. -/
  updC : Prog isa
  upd : Verified X86.target updC Proof.Sha256.updateX86
  updNoSp : NoSp updC
  updStack : stackUse updC ≤ 20
  finC : Prog isa
  fin : Verified X86.target finC Proof.Sha256.finalizeX86
  finNoSp : NoSp finC
  finStack : stackUse finC ≤ 20
  /-- What PBKDF2's whole derivation needs of the functions it calls: they
  keep `esp`, and use at most 48 bytes of stack. -/
  initNoSp : NoSp (Impl.Hmac.Sha256.X86.init cmpN cmpC)
  initStack : stackUse (Impl.Hmac.Sha256.X86.init cmpN cmpC) ≤ 48
  finalizeNoSp : NoSp (Impl.Hmac.Sha256.X86.finalize cmpN cmpC)
  finalizeStack : stackUse (Impl.Hmac.Sha256.X86.finalize cmpN cmpC) ≤ 48
  iterNoSp : NoSp (Impl.Pbkdf2.Sha256.X86.iterate cmpN cmpC)
  iterStack : stackUse (Impl.Pbkdf2.Sha256.X86.iterate cmpN cmpC) ≤ 48
  pbkdf2Sp : (Proof.Pbkdf2.Whole.X86.sha256Fns suffix cmpN cmpC updC finC).pbkdf2.all
    (fun i => !isa.writesSp i) = true

end VG.Proof.Sha256.X86.Variants
