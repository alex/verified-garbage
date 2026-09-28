import VerifiedGarbage.Spec.Poly1305
import VerifiedGarbage.TCB.Arm.Target

/-!
# Poly1305: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`).
-/

namespace VG.Proof.Poly1305

open Spec.Poly1305

open Arm in
/-- `vg_poly1305_init(state: *mut [u64; 16], key: *const [u8; 32])`. -/
def initArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let key : Region := ⟨State.addr (s.gpr .r1), 32⟩
    s.rd = [key] ∧ s.wr = [state] ∧ state.Disjoint key ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 32 ≤ 2 ^ 32
  post s s' := Repr s'.mem (State.addr (s.gpr .r0)) (bytesAt s.mem (State.addr (s.gpr .r1)) 32) []
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1

open Arm in
/-- `vg_poly1305_blocks(state: *mut [u64; 16], blocks: *const [u8; 16], n: usize)`. -/
def blocksArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let blocks : Region := ⟨State.addr (s.gpr .r1), 16 * (s.gpr .r2).toNat⟩
    s.rd = [blocks] ∧ s.wr = [state] ∧ state.Disjoint blocks ∧
      (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 16 * (s.gpr .r2).toNat ≤ 2 ^ 32
  post s s' := ∀ key msg, Repr s.mem (State.addr (s.gpr .r0)) key msg →
    Repr s'.mem (State.addr (s.gpr .r0)) key
      (msg ++ bytesAt s.mem (State.addr (s.gpr .r1)) (16 * (s.gpr .r2).toNat))
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2

open Arm in
/-- `vg_poly1305_finalize(state: *mut [u64; 16], tail: *const u8, len: usize, out: *mut [u8; 16])`. -/
def finalizeArm : Contract Arm.isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 128⟩
    let tail : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r3), 16⟩
    s.rd = [tail] ∧ s.wr = [state, out] ∧ state.Disjoint tail ∧ state.Disjoint out ∧
      tail.Disjoint out ∧ (s.gpr .r0).toNat + 128 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat < 16
  post s s' := ∀ key msg, Repr s.mem (State.addr (s.gpr .r0)) key msg →
    bytesAt s'.mem (State.addr (s.gpr .r3)) 16 =
      mac key (msg ++ bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3

end VG.Proof.Poly1305
