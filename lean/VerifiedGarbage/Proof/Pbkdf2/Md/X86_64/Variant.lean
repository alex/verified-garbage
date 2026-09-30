import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Core
import VerifiedGarbage.TCB.Artifact

/-!
# Merkle–Damgård hash functions on x86-64, as variants

Untrusted: everything here is checked by Lean.

An `MdHash` is one Merkle–Damgård hash function with one implementation of
its compression function: each is a variant of the interface `MdHash` on
x86-64 (`Variants/MdHash/X86_64/`), and each function built on the hash
function (in `Generic/MdHash/X86_64/`) is emitted once for each of them (see
`TCB/Emit.lean`): its streaming `update` and `finalize` (when they are not
shared by several variants, `stream`), HMAC's `init` and `finalize`, and
PBKDF2's `iterate` and `pbkdf2`, all named with the variant's `suffix`.

`MdHash.of` builds one from what the proofs need of the hash function's
code (`HashOK`), what the kernel checks of the code HMAC and PBKDF2 add to
it (`CoreOK`, once for each hash function) and of the functions they call
(`Callees`, once for each implementation), and the satisfiability of the
shared contracts, which the kernel checks for each instance.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- `Code.allInstrs p` from `Code.all p`. -/
theorem allInstrs_of_all {I C : Type} {p : I → Bool} {c : Code I C} (h : c.all p = true) :
    c.allInstrs p = true := by
  induction c with
  | block is => induction is <;> simp_all [Code.all, Code.allInstrs]
  | _ => simp_all [Code.all, Code.allInstrs]

/-- One of the streaming functions made with an implementation of a hash
function's compression function, which `Generic/MdHash/X86_64/Stream.lean`
emits, naming it with the variant's suffix: its `Api` (in `Spec/`), and its
code, verified against the contract the `Api` gives it (`ofApi`, as
`Artifact.ofApi`) with `stack` bytes of stack. -/
structure StreamFn where
  api : Api
  code : Prog X86_64.target.isa
  contract : Contract X86_64.target.isa
  stack : Nat := 0
  verified : Verified X86_64.target code contract
  ofSig : ∃ pre post leak,
      contract = api.sig.contract X86_64.target.abi pre post api.writeArgs stack leak := by
    exact ⟨_, _, _, rfl⟩
  ofApi : api.contracts.elim True fun f => contract = f X86_64.target.abi stack := by
    first | exact True.intro | exact rfl
  spSafe : code.all (fun i => !X86_64.target.isa.writesSp i) = true

/-- A Merkle–Damgård hash function on x86-64, with one implementation of its
compression function: its functions, verified against the contracts of its
instance `I` (`Spec/Hmac/Generic.lean`, `Spec/Pbkdf2/Generic.lean`). -/
structure MdHash where
  /-- The hash function's code and the names of its functions. -/
  H : Hash
  /-- The instance of the shared contracts. -/
  I : Spec.Hmac.Instance
  hmacInit : Verified X86_64.target H.hmacInit (I.initContract X86_64.abi 16)
  hmacFin : Verified X86_64.target H.hmacFin (I.finalizeContract X86_64.abi 16)
  iterate : Verified X86_64.target H.iterate (I.iterateContract X86_64.abi 8)
  pbkdf2 : Verified X86_64.target H.pbkdf2 (I.pbkdf2Contract X86_64.abi 24)
  hmacInitSp : H.hmacInit.all (fun i => !isa.writesSp i) = true
  hmacFinSp : H.hmacFin.all (fun i => !isa.writesSp i) = true
  iterateSp : H.iterate.all (fun i => !isa.writesSp i) = true
  pbkdf2Sp : H.pbkdf2.all (fun i => !isa.writesSp i) = true
  /-- What the names of the functions emitted for it end with (e.g.
  `_shani`; nothing for the baseline implementation). -/
  suffix : String
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String
  /-- The streaming `update` and `finalize` made with this implementation of
  the compression function, when no other variant shares them (otherwise
  they are in the hash function's registration file). -/
  stream : List StreamFn

namespace MdHash

variable {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
  (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
include hH C K hSH hW

theorem hmacInit_of (hs : ∃ s, (I.initContract X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacInit (I.initContract X86_64.abi 16) := by
  simp only [Spec.Hmac.Instance.initContract, ← hSH, ← hW] at hs ⊢
  exact hmacInit_verified hH C K hs

theorem hmacFin_of (hs : ∃ s, (I.finalizeContract X86_64.abi 16).pre s) :
    Verified X86_64.target H.hmacFin (I.finalizeContract X86_64.abi 16) := by
  simp only [Spec.Hmac.Instance.finalizeContract, ← hSH, ← hW] at hs ⊢
  exact hmacFin_verified hH C K hs

theorem iterate_of (hs : ∃ s, (I.iterateContract X86_64.abi 8).pre s) :
    Verified X86_64.target H.iterate (I.iterateContract X86_64.abi 8) := by
  simp only [Spec.Hmac.Instance.iterateContract, ← hSH, ← hW] at hs ⊢
  exact iterate_verified hH C K hs

theorem pbkdf2_of (hsI : ∃ s, (I.initContract X86_64.abi 16).pre s)
    (hsF : ∃ s, (I.finalizeContract X86_64.abi 16).pre s)
    (hsT : ∃ s, (I.iterateContract X86_64.abi 8).pre s)
    (hs : ∃ s, (I.pbkdf2Contract X86_64.abi 24).pre s) :
    Verified X86_64.target H.pbkdf2 (I.pbkdf2Contract X86_64.abi 24) := by
  simp only [Spec.Hmac.Instance.initContract, Spec.Hmac.Instance.finalizeContract,
    Spec.Hmac.Instance.iterateContract, Spec.Hmac.Instance.pbkdf2Contract,
    Spec.Hmac.Instance.pbkdf2Scratch, ← hSH, ← hW, hH.hS] at hsI hsF hsT hs ⊢
  exact pbkdf2_verified hH C K hsI hsF hsT hs

end MdHash

/-- The variant of hash function `H`, of instance `I`, from what the proofs
need of it and the satisfiability of the shared contracts. -/
def MdHash.of {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H)) (K : Callees H)
    (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
    (hsI : ∃ s, (I.initContract X86_64.abi 16).pre s)
    (hsF : ∃ s, (I.finalizeContract X86_64.abi 16).pre s)
    (hsT : ∃ s, (I.iterateContract X86_64.abi 8).pre s)
    (hsP : ∃ s, (I.pbkdf2Contract X86_64.abi 24).pre s)
    (suffix : String) (features : List String) (stream : List StreamFn) : MdHash where
  H := H
  I := I
  hmacInit := MdHash.hmacInit_of hH C K hSH hW hsI
  hmacFin := MdHash.hmacFin_of hH C K hSH hW hsF
  iterate := MdHash.iterate_of hH C K hSH hW hsT
  pbkdf2 := MdHash.pbkdf2_of hH C K hSH hW hsI hsF hsT hsP
  hmacInitSp := hmacInit_sp C K
  hmacFinSp := hmacFin_sp C K
  iterateSp := iterate_sp C K
  pbkdf2Sp := pbkdf2_sp C K
  suffix := suffix
  features := features
  stream := stream

end VG.Proof.Pbkdf2.Md.X86_64
