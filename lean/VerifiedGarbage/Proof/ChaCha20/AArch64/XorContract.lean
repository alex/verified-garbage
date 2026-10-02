import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.ChaCha20.Contract
import VerifiedGarbage.Proof.ChaCha20.Keystream
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.ChaCha20.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ChaCha20 keystream XOR on AArch64
-/

namespace VG.Proof.ChaCha20

open Spec.ChaCha20 VG.AArch64

/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
AArch64 contract for
`vg_chacha20_xor(state: *mut [u32; 16], data: *mut u8, len: usize, buf: *mut [u32; 80])`:
XORs the first `len` bytes of the keystream of the state at `state` into the
`len` bytes at `data`.

The code may read and write `state` (64 bytes; its contents on exit are
unspecified), `data` (`len` bytes) and `buf` (320 bytes of working space).
They may not overlap each other; `data` does not wrap around the end of the
address space. The return address is in `x30`, not on the stack, and the
code uses no stack. The pointers and the length are public; the state and
the data are secret. -/
def xorAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 64⟩
    let data : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let buf : Region := ⟨s.gpr .x3, 320⟩
    s.rd = [] ∧ s.wr = [state, data, buf] ∧
    state.Disjoint data ∧ state.Disjoint buf ∧ data.Disjoint buf ∧
    (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' :=
    bytesAt s'.mem (s.gpr .x1) (s.gpr .x2).toNat =
      List.zipWith (· ^^^ ·) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
        (keystream (stateAt s.mem (s.gpr .x0)) (s.gpr .x2).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.ChaCha20

