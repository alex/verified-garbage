import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.AArch64.Target

/-!
# ChaCha20-Poly1305: the AArch64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`). The return address is in the link register `x30`, and
calls store nothing in memory, so no stack is involved.
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open AArch64 in
/-- The precondition of both functions: `ctx` (1024 bytes) and `data` may be
read and written, `aad` read; none of them overlaps another; nothing wraps
around the end of the address space. -/
def preAArch64 (s : AArch64.State) : Prop :=
  let ctx : Region := ⟨s.gpr .x0, 1024⟩
  let aad : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
  let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
  s.rd = [aad] ∧ s.wr = [ctx, data] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧
  (s.gpr .x0).toNat + 1024 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
  (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64

open AArch64 in
def pubAArch64 (s₁ s₂ : AArch64.State) : Prop :=
  s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
  s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

open AArch64 in
/-- `vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealAArch64 : Contract AArch64.isa where
  pre := preAArch64
  post s s' :=
    let ctx := s.gpr .x0
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat) =
      (bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubAArch64

open AArch64 in
/-- `vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openAArch64 : Contract AArch64.isa where
  pre := preAArch64
  post s s' :=
    let ctx := s.gpr .x0
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) (bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
        (bytesAt s.mem (ctx + 48) 16) with
    | some pt => (s'.gpr .x0).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .x3) (s.gpr .x4).toNat = pt
    | none => (s'.gpr .x0).setWidth 32 = 0
  pub := pubAArch64

end VG.Proof.ChaCha20Poly1305
