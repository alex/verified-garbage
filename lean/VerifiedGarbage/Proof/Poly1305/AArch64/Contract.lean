import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.AArch64.Target

/-!
# Poly1305: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`). The return address is in the link register `x30`,
which the calling convention requires to be preserved, not on the stack.
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open AArch64 in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let key : Region := ⟨s.gpr .x1, 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key
  post s s' := Repr s'.mem (s.gpr .x0) (bytesAt s.mem (s.gpr .x1) 32) []
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let blocks : Region := ⟨s.gpr .x1, 16 * (s.gpr .x2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .x1).toNat + 16 * (s.gpr .x2).toNat ≤ 2 ^ 64
  post s s' := ∀ key msg, Repr s.mem (s.gpr .x0) key msg →
    Repr s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x1) (16 * (s.gpr .x2).toNat))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

open AArch64 in
/-- `vg_poly1305_update(state: *mut [u64; 16], count: u64, data: *const u8, len: usize, …)`:
only `count mod 16`, the number of bytes buffered, matters. The state must be
writable, and it may be permitted to write other regions (which it does
not). -/
def updateAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    s.rd = [data] ∧ state ∈ s.wr ∧ state.Disjoint data
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 →
    Buffered s'.mem (s.gpr .x0) key (msg ++ bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], count: u64, out: *mut [u8; 16], …)`:
only `count mod 16`, the number of bytes buffered, matters. The state and
`out` must be writable, and it may be permitted to write other regions
(which it does not). -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let out : Region := ⟨s.gpr .x2, 16⟩
    state ∈ s.wr ∧ out ∈ s.wr ∧ state.Disjoint out
  post s s' := ∀ key msg, Buffered s.mem (s.gpr .x0) key msg →
    (s.gpr .x1).toNat % 16 = msg.length % 16 → bytesAt s'.mem (s.gpr .x2) 16 = mac key msg
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.sp = s₂.sp

end VG.Proof.Poly1305
