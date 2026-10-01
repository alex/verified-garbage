import VerifiedGarbage.Spec.Ct
import VerifiedGarbage.TCB.Artifact

/-!
# Constant-time comparison: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_ct_eq`, in terms
of `Spec/Ct.lean`, for any target: `A` is the target's calling convention.
The signature fixes where the arguments are, the memory the function may
access (it reads the two buffers and writes none), and that the pointers and
lengths are public (see `TCB/Sig.lean`); the contract adds the rest. The
bytes compared are secret.

Each buffer is a slice with a length of its own, since a `Sig` slice carries
its own length: the function compares the byte strings, so buffers of
different lengths are unequal, as Rust's `==` on slices says. The lengths
are public, so the function may return early when they differ; it may not
when the bytes differ. The buffers are only read, so they may overlap (or
be the same).

The result, 1 or 0, is a `u32` as `vg_chacha20_poly1305_open`'s is. It
depends on the secret bytes (it is what the function computes), but the
constant-time obligation of `Verified` is on the leakage trace (addresses
and branches), which may depend only on the pointers and the lengths: two
calls with the same pointers and lengths take the same path whatever the
bytes, and differ only in the value returned.

The contract takes the number of bytes of stack below the stack pointer that
an implementation's frames use (`stack`, see `Sig.contract`), 0 for one that
uses none.
-/

namespace VG.Spec.Ct

/-- `vg_ct_eq(a: *const u8, a_len: usize, b: *const u8, b_len: usize) -> u32`. -/
def eqSig : Sig where
  params := [("a", .slice false .u8 "a_len"), ("b", .slice false .u8 "b_len")]
  ret := some .u32

/-- Returns 1 if the `a_len` bytes at `a` are the `b_len` bytes at `b` (so
`a_len = b_len`), and 0 otherwise. -/
def eqContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  eqSig.contract A (post := fun a aLen b bLen m _m' r =>
    r = if eq (bytesAt m a aLen.toNat) (bytesAt m b bLen.toNat) then 1 else 0)
    (stack := stack)

/-- `vg_ct_eq` on every target. -/
def eqApi : Api where
  module := "ct"
  name := "vg_ct_eq"
  sig := eqSig
  summary := "Compares two byte strings in constant time: returns 1 if the `a_len` bytes at `a` \
    are the `b_len` bytes at `b` (so byte strings of different lengths are unequal), and 0 \
    otherwise. Writes no memory.\n\n\
    Contract: `VG.Spec.Ct.eqContract`. Constant time: only the pointers, `a_len` and `b_len` may \
    affect timing, not the bytes compared; only the result depends on them."
  safety := []

end VG.Spec.Ct
