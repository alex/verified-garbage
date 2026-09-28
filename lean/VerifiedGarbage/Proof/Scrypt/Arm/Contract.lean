import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.Arm.Target

/-!
# scrypt: the 32-bit ARM contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are
emitted with the shared contracts of `Spec/Scrypt/Contract.lean`, which imply
these (`Contract.Implies`).

Under AAPCS the first four argument words are in `r0`–`r3` and the others on
the stack (`stackArg`), which the code may read but not write. None of the
functions uses the stack otherwise: calls leave the return address in `lr`,
and each function saves what it must in its scratch space.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open Arm in
/-- 32-bit ARM contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32; 16])`:
replaces the 64 bytes at `b` by their Salsa20/8 Core.

The code may read and write `b` (in `r0`) and `scratch` (in `r1`; 64 bytes
each, the contents of `scratch` on exit unspecified), which may not overlap
or wrap around the end of the address space. The pointers are public; the
data is secret. -/
def salsaArm : Contract Arm.isa where
  pre s :=
    let b : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let scratch : Region := ⟨State.addr (s.gpr .r1), 64⟩
    s.rd = [] ∧ s.wr = [b, scratch] ∧ b.Disjoint scratch ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r0)) 64 =
    salsa (bytesAt s.mem (State.addr (s.gpr .r0)) 64)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.sp = s₂.sp

open Arm in
/-- 32-bit ARM contract for
`vg_scrypt_blockmix(b = r0, r = r1, y = r2, ry = r3, scratch = [sp])`:
if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at `b` to `y`.
The code may read `b` and the stack argument, and read and write `y` and
`scratch` (128 bytes). -/
def blockMixArm : Contract Arm.isa where
  pre s :=
    let r := (s.gpr .r1).toNat
    let b : Region := ⟨State.addr (s.gpr .r0), r * 128⟩
    let y : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 128⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [b, args] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧ args.Disjoint y ∧
    args.Disjoint scratch ∧
    (s.gpr .r0).toNat + r * 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    s.gpr .r3 = s.gpr .r1 ∧ 0 < r
  post s s' := let r := (s.gpr .r1).toNat
    bytesAt s'.mem (State.addr (s.gpr .r2)) (128 * r) =
      blockMix r (bytesAt s.mem (State.addr (s.gpr .r0)) (128 * r))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open Arm in
/-- 32-bit ARM contract for
`vg_scrypt_romix(b = r0, r = r1, v = r2, vlen = r3, scratch = [sp], slen = [sp + 4])`:
if `r > 0`, `vlen = N r` for a power of two `N`, and `slen = r + 2`, replaces
the `128 r` bytes at `b` by their scryptROMix. The code may read the stack
arguments, and read and write `b`, `v` and `scratch`. The indices `j` of
step 3 are public. -/
def roMixArm : Contract Arm.isa where
  pre s :=
    let r := (s.gpr .r1).toNat
    let b : Region := ⟨State.addr (s.gpr .r0), r * 128⟩
    let v : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 128⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat * 128⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    args.Disjoint b ∧ args.Disjoint v ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + r * 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat * 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    0 < r ∧ (s.gpr .r3).toNat % r = 0 ∧ ((s.gpr .r3).toNat / r).isPowerOfTwo ∧
    (stackArg s 1).toNat = r + 2
  post s s' := let r := (s.gpr .r1).toNat
    bytesAt s'.mem (State.addr (s.gpr .r0)) (128 * r) =
      roMix r ((s.gpr .r3).toNat / r) (bytesAt s.mem (State.addr (s.gpr .r0)) (128 * r))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧
    roMixIndices (s₁.gpr .r1).toNat ((s₁.gpr .r3).toNat / (s₁.gpr .r1).toNat)
        (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (128 * (s₁.gpr .r1).toNat)) =
      roMixIndices (s₂.gpr .r1).toNat ((s₂.gpr .r3).toNat / (s₂.gpr .r1).toNat)
        (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (128 * (s₂.gpr .r1).toNat))

end VG.Proof.Scrypt
