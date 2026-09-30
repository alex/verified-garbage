import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Core
import VerifiedGarbage.TCB.Artifact

/-!
# Merkle–Damgård hash functions on AArch64, as variants

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Pbkdf2/Md/X86_64/Variant.lean`): an `MdHash` is one Merkle–Damgård
hash function with one implementation of its compression function, a
variant of the interface `MdHash` on AArch64 (`Variants/MdHash/AArch64/`),
and each function built on the hash function (in `Generic/MdHash/AArch64/`)
is emitted once for each of them: HMAC's `init` and `finalize`, and
PBKDF2's `iterate` and `pbkdf2`, named with the variant's `suffix`.

`MdHash.of` builds one from what the proofs need of the hash function's
code (`HashOK`), what the kernel checks of the code HMAC and PBKDF2 add to
it (`CoreOK`, once for each hash function), and the satisfiability of the
shared contracts, which the kernel checks for each instance.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)

/-- A Merkle–Damgård hash function on AArch64, with one implementation of
its compression function: its functions, verified against the contracts of
its instance `I` (`Spec/Hmac/Generic.lean`, `Spec/Pbkdf2/Generic.lean`). -/
structure MdHash where
  /-- The hash function's code and the names of its functions. -/
  H : Hash
  /-- The instance of the shared contracts. -/
  I : Spec.Hmac.Instance
  hmacInit : Verified AArch64.target H.hmacInit (I.initContract AArch64.abi 16)
  hmacFin : Verified AArch64.target H.hmacFin (I.finalizeContract AArch64.abi 16)
  iterate : Verified AArch64.target H.iterate (I.iterateContract AArch64.abi)
  pbkdf2 : Verified AArch64.target H.pbkdf2 (I.pbkdf2Contract AArch64.abi 16)
  /-- What the names of the functions emitted for it end with (nothing for
  the baseline implementation). -/
  suffix : String
  /-- The CPU features its compression function requires, which the
  functions built on it require too. -/
  features : List String

namespace MdHash

variable {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H))
  (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
include hH C hSH hW

theorem hmacInit_of (hs : ∃ s, (I.initContract AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacInit (I.initContract AArch64.abi 16) := by
  simp only [Spec.Hmac.Instance.initContract, ← hSH, ← hW] at hs ⊢
  exact hmacInit_verified hH C hs

theorem hmacFin_of (hs : ∃ s, (I.finalizeContract AArch64.abi 16).pre s) :
    Verified AArch64.target H.hmacFin (I.finalizeContract AArch64.abi 16) := by
  simp only [Spec.Hmac.Instance.finalizeContract, ← hSH, ← hW] at hs ⊢
  exact hmacFin_verified hH C hs

theorem iterate_of (hs : ∃ s, (I.iterateContract AArch64.abi).pre s) :
    Verified AArch64.target H.iterate (I.iterateContract AArch64.abi) := by
  simp only [Spec.Hmac.Instance.iterateContract, ← hSH, ← hW] at hs ⊢
  exact iterate_verified hH C hs

theorem pbkdf2_of (hsI : ∃ s, (I.initContract AArch64.abi 16).pre s)
    (hsF : ∃ s, (I.finalizeContract AArch64.abi 16).pre s)
    (hsT : ∃ s, (I.iterateContract AArch64.abi).pre s)
    (hs : ∃ s, (I.pbkdf2Contract AArch64.abi 16).pre s) :
    Verified AArch64.target H.pbkdf2 (I.pbkdf2Contract AArch64.abi 16) := by
  simp only [Spec.Hmac.Instance.initContract, Spec.Hmac.Instance.finalizeContract,
    Spec.Hmac.Instance.iterateContract, Spec.Hmac.Instance.pbkdf2Contract,
    Spec.Hmac.Instance.pbkdf2Scratch, ← hSH, ← hW, hH.hS] at hsI hsF hsT hs ⊢
  exact pbkdf2_verified hH C hsI hsF hsT hs

end MdHash

/-- The variant of hash function `H`, of instance `I`, from what the proofs
need of it and the satisfiability of the shared contracts. -/
def MdHash.of {H : Hash} {I : Spec.Hmac.Instance} (hH : HashOK H) (C : CoreOK (core H))
    (hSH : hH.SH = I.S) (hW : H.W = I.scratch)
    (hsI : ∃ s, (I.initContract AArch64.abi 16).pre s)
    (hsF : ∃ s, (I.finalizeContract AArch64.abi 16).pre s)
    (hsT : ∃ s, (I.iterateContract AArch64.abi).pre s)
    (hsP : ∃ s, (I.pbkdf2Contract AArch64.abi 16).pre s)
    (suffix : String) (features : List String) : MdHash where
  H := H
  I := I
  hmacInit := MdHash.hmacInit_of hH C hSH hW hsI
  hmacFin := MdHash.hmacFin_of hH C hSH hW hsF
  iterate := MdHash.iterate_of hH C hSH hW hsT
  pbkdf2 := MdHash.pbkdf2_of hH C hSH hW hsI hsF hsT hsP
  suffix := suffix
  features := features

end VG.Proof.Pbkdf2.Md.AArch64
