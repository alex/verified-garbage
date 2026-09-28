import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# The Salsa20/8 Core: the x86-64 contract

**Untrusted**: the contract the proof is written against; the artifact is
emitted with the shared contract of `Spec/Scrypt/Contract.lean`, which implies
this one (`Contract.Implies`).
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

end VG.Proof.Scrypt
