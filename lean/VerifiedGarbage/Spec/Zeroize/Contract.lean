import VerifiedGarbage.Spec.Zeroize
import VerifiedGarbage.TCB.Artifact

/-!
# Zeroization: the contract, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_zeroize`, in
terms of `Spec/Zeroize.lean`, for any target: `A` is the target's calling
convention. The signature fixes where the arguments are, the memory the
function may access, and that the pointer and the length are public (see
`TCB/Sig.lean`); the contract adds the rest. The bytes wiped are secret.

The function writes no memory but the buffer: `Sig.contract` lets it write
only its one writable buffer (and the stack below the stack pointer that its
frames use, where no Rust object lies), and every ISA model faults on a store
outside the regions it may write. So the postcondition need only say what
the buffer holds afterwards.

The contract takes the number of bytes of stack below the stack pointer that
an implementation's frames use (`stack`, see `Sig.contract`), 0 for one that
uses none.
-/

namespace VG.Spec.Zeroize

/-- `vg_zeroize(p: *mut u8, len: usize)`. -/
def zeroizeSig : Sig where
  params := [("p", .slice true .u8 "len")]

/-- Sets the `len` bytes at `p` to zero. -/
def zeroizeContract {M : ISA} (A : Abi M) (stack : Nat := 0) : Contract M :=
  zeroizeSig.contract A (post := fun p len _m m' _ => bytesAt m' p len.toNat = zeros len.toNat)
    (stack := stack)

/-- `vg_zeroize` on every target. -/
def zeroizeApi : Api where
  module := "zeroize"
  name := "vg_zeroize"
  sig := zeroizeSig
  contracts := some fun A stack => zeroizeContract A stack
  summary := "Wipes a buffer: sets the `len` bytes at `p` to zero, and writes no other memory. \
    A call of it is not a dead store the compiler may remove, since the compiler cannot see its \
    code.\n\n\
    Contract: `VG.Spec.Zeroize.zeroizeContract`. Constant time: only `p` and `len` may affect \
    timing, not the bytes wiped."
  safety := []

end VG.Spec.Zeroize
