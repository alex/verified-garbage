import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.X86_64.Target

/-!
# ChaCha20-Poly1305: the x86-64 contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`).
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open X86_64 in
/-- The precondition of both functions: `ctx` (1024 bytes) and `data` may be
read and written, `aad` read; none of them overlaps another (`aad` may overlap
nothing writable), the return address or the 16 bytes of stack below it, where
the calls store their return addresses; nothing wraps around the end of the
address space. -/
def preX86_64 (s : X86_64.State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 1024⟩
  let aad : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
  let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
  s.rd = [aad] ∧ s.wr = [ctx, data] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧
  ret.Disjoint ctx ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧
  stack.Disjoint ctx ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  (s.gpr .rdi).toNat + 1024 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
  (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64

open X86_64 in
def pubX86_64 (s₁ s₂ : X86_64.State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
  s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

open X86_64 in
/-- `vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealX86_64 : Contract X86_64.isa where
  pre := preX86_64
  post s s' :=
    let ctx := s.gpr .rdi
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) =
      (bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubX86_64

open X86_64 in
/-- `vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openX86_64 : Contract X86_64.isa where
  pre := preX86_64
  post s s' :=
    let ctx := s.gpr .rdi
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) (bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
        (bytesAt s.mem (ctx + 48) 16) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0
  pub := pubX86_64

end VG.Proof.ChaCha20Poly1305
