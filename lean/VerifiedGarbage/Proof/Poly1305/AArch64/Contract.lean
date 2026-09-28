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
/-- `vg_poly1305_finalize(state: *mut [u64; 16], tail: *const u8, len: usize, out: *mut [u8; 16])`. -/
def finalizeAArch64 : Contract AArch64.isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 128⟩
    let tail : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let out : Region := ⟨s.gpr .x3, 16⟩
    s.rd = [tail] ∧ s.wr = [state, out] ∧ state.Disjoint tail ∧ state.Disjoint out ∧
      tail.Disjoint out ∧ (s.gpr .x2).toNat < 16
  post s s' := ∀ key msg, Repr s.mem (s.gpr .x0) key msg →
    bytesAt s'.mem (s.gpr .x3) 16 = mac key (msg ++ bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧
    s₁.gpr .x2 = s₂.gpr .x2 ∧ s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

end VG.Proof.Poly1305
