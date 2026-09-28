import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# scrypt: the x86-64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts are
emitted with the shared contracts of `Spec/Scrypt/Contract.lean`, which imply
these (`Contract.Implies`).
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open X86_64 in
/-- x86-64 contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32; 16])`:
replaces the 64 bytes at `b` by their Salsa20/8 Core.

The code may read and write `b` and `scratch` (64 bytes each; the contents of
`scratch` on exit are unspecified), which may not overlap each other or the
return address on the stack. The pointers are public; the data is secret. -/
def salsaX86_64 : Contract X86_64.isa where
  pre s :=
    let b : Region := ⟨s.gpr .rdi, 64⟩
    let scratch : Region := ⟨s.gpr .rsi, 64⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [] ∧ s.wr = [b, scratch] ∧ b.Disjoint scratch ∧ ret.Disjoint b ∧ ret.Disjoint scratch
  post s s' := bytesAt s'.mem (s.gpr .rdi) 64 = salsa (bytesAt s.mem (s.gpr .rdi) 64)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi

open X86_64 in
/-- x86-64 contract for `vg_scrypt_blockmix(b = rdi, r = rsi, y = rdx, ry = rcx, scratch = r8)`:
if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at `b` to `y`.
Its call of `vg_salsa20_8` stores a return address in the 8 bytes below the
stack pointer. -/
def blockMixX86_64 : Contract X86_64.isa where
  pre s :=
    let r := (s.gpr .rsi).toNat
    let b : Region := ⟨s.gpr .rdi, r * 128⟩
    let y : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 128⟩
    let scratch : Region := ⟨s.gpr .r8, 128⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
    s.rd = [b] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧
    ret.Disjoint y ∧ ret.Disjoint scratch ∧
    stack.Disjoint b ∧ stack.Disjoint y ∧ stack.Disjoint scratch ∧
    (s.gpr .rdi).toNat + r * 128 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat * 128 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + 128 ≤ 2 ^ 64 ∧
    s.gpr .rcx = s.gpr .rsi ∧ 0 < r
  post s s' := let r := (s.gpr .rsi).toNat
    bytesAt s'.mem (s.gpr .rdx) (128 * r) = blockMix r (bytesAt s.mem (s.gpr .rdi) (128 * r))
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Scrypt
