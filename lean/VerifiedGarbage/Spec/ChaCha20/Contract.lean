import VerifiedGarbage.Spec.ChaCha20
import VerifiedGarbage.TCB.Artifact

/-!
# ChaCha20: the contract of the block function, on every target

**Trusted** (as every file in `Spec/`). The contract of `vg_chacha20_block`,
in terms of `Spec/ChaCha20.lean`, for any target: `A` is the target's
calling convention. The signature fixes where the arguments are, the memory
the function may access, disjointness, and that the pointers are public (see
`TCB/Sig.lean`).
-/

namespace VG.Spec.ChaCha20

/-- `vg_chacha20_block(state: *const [u32; 16], buf: *mut [u32; 64])`. The
first 16 words of `buf` hold the result on exit; the rest is working space. -/
def blockSig : Sig where
  params := [("state", .array false .u32 16), ("buf", .array true .u32 64)]

/-- Writes `block` of the state at `state` to the first 16 words of `buf`.
The state (key, counter and nonce) is secret. -/
def blockContract {M : ISA} (A : Abi M) : Contract M :=
  blockSig.contract A (post := fun state buf m m' _ =>
    stateAt m' buf = block (stateAt m state))

end VG.Spec.ChaCha20
