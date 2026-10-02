import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Generic.X86.Instances
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.TCB.Artifact

/-!
# SHA-256 backends on x86

Untrusted: everything here is checked by Lean.

A backend is one implementation of SHA-256's compression function on x86: a
variant of the interface `Sha256` on x86 (`Variants/Sha256/X86/`). Each
function built on it (in `Generic/Sha256/X86/`) is emitted once for each
backend, named with its suffix (see `TCB/Emit.lean`): its own functions, the
compression function and the streaming ones made with it (`functions`), and
HMAC's `init` and `finalize` and PBKDF2's `iterate`, the one implementation
for every streaming hash function (`Impl/Hmac/Generic/X86.lean`,
`Impl/Pbkdf2/Generic/X86.lean`), calling the backend's streaming `update` and
`finalize` (`stream`). Those are proven once for every backend, against the
contracts of `Spec.Hmac.sha256I` (`Proof/Hmac/Generic/X86/Instances.lean`,
`Proof/Pbkdf2/Generic/X86/Instances.lean`), from what `stream` says of its
streaming functions (`Proof/Sha256/X86/Stream/Variant.lean` proves it for any
verified compression function). So adding an implementation of the
compression function also emits the SHA-256, HMAC and PBKDF2 functions that
call it.
-/
namespace VG.Proof.Sha256.X86.Variants

open VG.X86
open VG.Proof.Hmac.Generic.X86 (Sha256Stream sha256H)

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
  /-- SHA-256's streaming `update` and `finalize` made with this
  implementation, as HMAC and PBKDF2 call them, and the suffix of the names
  of the functions emitted for it (e.g. `_shani`; nothing for the baseline
  implementation). -/
  stream : Sha256Stream
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- Its own functions: the compression function and the streaming
  functions made with it. -/
  functions : List StreamFn
  initSp : (sha256H stream).init.all (fun i => !isa.writesSp i) = true
  finSp : (sha256H stream).finalize.all (fun i => !isa.writesSp i) = true
  iterSp : (Impl.Pbkdf2.Generic.X86.iterate (sha256H stream)).all (fun i => !isa.writesSp i) = true

namespace Backend

variable (v : Backend)

/-- What the names of the functions emitted for it end with. -/
def suffix : String := v.stream.suffix

/-- SHA-256's functions, as HMAC and PBKDF2 call them. -/
def H : Impl.Hmac.Generic.X86.Hash := sha256H v.stream

theorem hmacInit : Verified X86.target v.H.init (Spec.Hmac.sha256I.initContract X86.abi 48) :=
  Proof.Hmac.Generic.X86.Instances.sha256_init v.stream

theorem hmacFin : Verified X86.target v.H.finalize (Spec.Hmac.sha256I.finalizeContract X86.abi 48) :=
  Proof.Hmac.Generic.X86.Instances.sha256_finalize v.stream

theorem iterate : Verified X86.target (Impl.Pbkdf2.Generic.X86.iterate v.H)
    (Spec.Hmac.sha256I.iterateContract X86.abi 48) :=
  Proof.Pbkdf2.Generic.X86.Instances.sha256 v.stream

end Backend

end VG.Proof.Sha256.X86.Variants
