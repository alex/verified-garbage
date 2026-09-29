import VerifiedGarbage.Spec.ChaCha20Poly1305
import VerifiedGarbage.TCB.X86.Target

/-!
# ChaCha20-Poly1305: the x86 (32-bit) contracts

**Untrusted**: the contracts the proofs are written against; the artifacts
are emitted with the shared contracts of `Spec/`, which imply these
(`Contract.Implies`). The arguments are on the stack (cdecl): `ctx`, `aad`,
`aad_len`, `data` and `len`.
-/

namespace VG.Proof.ChaCha20Poly1305

open Spec.ChaCha20Poly1305
open Spec.Poly1305 (bytesAt)

open X86 in
/-- The precondition of both functions: `ctx` (1024 bytes), `data` and the
arguments (20 bytes above the return address) may be read and written, `aad`
read; none of them overlaps another, and `ctx`, `aad` and `data` do not
overlap the return address or the 32 bytes of stack below it, where the calls
store their arguments and return addresses (and `vg_chacha20_xor` those of
its own calls); nothing wraps around the end of the address space. -/
def preX86 (s : X86.State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 1024⟩
  let aad : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
  let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
  let args : Region := ⟨argAddr s 0, 20⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 32, 32⟩
  s.rd = [aad] ∧ s.wr = [ctx, data, args] ∧
  ctx.Disjoint aad ∧ ctx.Disjoint data ∧ aad.Disjoint data ∧
  args.Disjoint ctx ∧ args.Disjoint aad ∧ args.Disjoint data ∧
  ret.Disjoint ctx ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧
  stack.Disjoint ctx ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  (arg s 0).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
  (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ 32 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

open X86 in
def pubX86 (s₁ s₂ : X86.State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

open X86 in
/-- `vg_chacha20_poly1305_seal(ctx, aad, aad_len, data, len)`. -/
def sealX86 : Contract X86.isa where
  pre := preX86
  post s s' :=
    let ctx := (arg s 0).setWidth 64
    encrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) =
      (bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat, bytesAt s'.mem (ctx + 48) 16)
  pub := pubX86

open X86 in
/-- `vg_chacha20_poly1305_open(ctx, aad, aad_len, data, len) -> u32`. -/
def openX86 : Contract X86.isa where
  pre := preX86
  post s s' :=
    let ctx := (arg s 0).setWidth 64
    match decrypt (bytesAt s.mem ctx 32) (bytesAt s.mem (ctx + 32) 12)
        (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat)
        (bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat) (bytesAt s.mem (ctx + 48) 16) with
    | some pt => s'.gpr .eax = 1 ∧ bytesAt s'.mem ((arg s 3).setWidth 64) (arg s 4).toNat = pt
    | none => s'.gpr .eax = 0
  pub := pubX86

end VG.Proof.ChaCha20Poly1305
