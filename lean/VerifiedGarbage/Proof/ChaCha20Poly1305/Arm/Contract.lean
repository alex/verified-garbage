import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.Arm.Target

/-!
# ChaCha20-Poly1305: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`). Under AAPCS, `ctx`, `aad`, `aad_len` and `data` are in
`r0`–`r3`, and `len` is the stack argument 0. The functions push 8 bytes of
stack (the stack arguments of `vg_poly1305_finalize`), which no buffer
overlaps.
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open Arm in
/-- The precondition of both functions: `ctx` (1024 bytes) and `data` may be
read and written, `aad` and the stack argument read; the written ones overlap
nothing else; none of them overlaps the 8 bytes below the stack pointer;
nothing wraps around the end of the address space. -/
def preArm (s : Arm.State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 1024⟩
  let aad : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
  let data : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
  let args : Region := ⟨stackArgAddr s 0, 4⟩
  let below : Region := ⟨State.addr s.sp - 8, 8⟩
  s.rd = [aad, args] ∧ s.wr = [ctx, data] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧ ctx.Disjoint args ∧ data.Disjoint args ∧
  below.Disjoint ctx ∧ below.Disjoint aad ∧ below.Disjoint data ∧
  (s.gpr .r0).toNat + 1024 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
  (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32

open Arm in
def pubArm (s₁ s₂ : Arm.State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
  s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open Arm in
/-- `vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealArm : Contract Arm.isa where
  pre := preArm
  post s s' :=
    let ctx := State.addr (s.gpr .r0)
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) =
      (bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubArm

open Arm in
/-- `vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openArm : Contract Arm.isa where
  pre := preArm
  post s s' :=
    let ctx := State.addr (s.gpr .r0)
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat)
        (bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat) (bytesAt s.mem (ctx + 48) 16) with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat = pt
    | none => s'.gpr .r0 = 0
  pub := pubArm

end VG.Proof.ChaCha20Poly1305
