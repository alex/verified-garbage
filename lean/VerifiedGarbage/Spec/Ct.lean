import VerifiedGarbage.TCB.Mem

/-!
# Constant-time comparison of byte strings

**Trusted** (as every file in `Spec/`). Not a cryptographic algorithm: the
comparison of two byte strings that a MAC's or an AEAD's verification makes
between a received tag and the one it computes, which must not reveal
through its timing where the two first differ (else a forger can find a
valid tag a byte at a time).

The function's result is the only thing that may depend on the bytes: its
contract (`Spec/Ct/Contract.lean`) says what it returns, and, as every
contract without `leak`, that its timing depends only on its public
arguments, the pointers and the lengths.

This file is independent of any architecture; the contract on every target
is in `Spec/Ct/Contract.lean`.
-/

namespace VG.Spec.Ct

/-- The `n` bytes at `p`. -/
def bytesAt (m : Mem) (p : Addr) (n : Nat) : List Byte :=
  (List.range n).map fun i => m (p + BitVec.ofNat 64 i)

/-- Whether two byte strings are equal: they have the same length and the
same bytes. -/
def eq (a b : List Byte) : Bool := a == b

end VG.Spec.Ct
