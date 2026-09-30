import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Hash

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s contract

Untrusted: everything here is checked by Lean. `pbkG` is the contract the
proof of `pbkdf2` is written against: `VG.Spec.Pbkdf2.pbkdf2Contract` with its
facts spelt out, which it implies for any streaming hash function and
scratch space (`generic_implies`). Every argument is in a register, and the
functions `pbkdf2` calls may use the 16 bytes below the stack pointer.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Proof.Hmac.Generic.AArch64 (stk)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

variable (S : StreamingHash) (W : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`,
with `8 W` bytes of scratch space. -/
def pbkG : Contract isa where
  pre s :=
    let pw : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let salt : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let out : Region := ⟨s.gpr .x5, (s.gpr .x6).toNat⟩
    let scratch : Region := ⟨s.gpr .x7, W * 8⟩
    16 ≤ s.sp.toNat ∧ s.rd = [pw, salt] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧
    (stk s).Disjoint pw ∧ (stk s).Disjoint salt ∧ (stk s).Disjoint out ∧ (stk s).Disjoint scratch ∧
    (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
    (s.gpr .x5).toNat + (s.gpr .x6).toNat ≤ 2 ^ 64 ∧ (s.gpr .x7).toNat + W * 8 ≤ 2 ^ 64 ∧
    0 < ((s.gpr .x4).setWidth 32).toNat ∧ (s.gpr .x6).toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac S (bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
      (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat) ((s.gpr .x4).setWidth 32).toNat (s.gpr .x6).toNat =
      some (bytesAt s'.mem (s.gpr .x5) (s.gpr .x6).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ (s₁.gpr .x4).setWidth 32 = (s₂.gpr .x4).setWidth 32 ∧
    s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.gpr .x6 = s₂.gpr .x6 ∧ s₁.gpr .x7 = s₂.gpr .x7 ∧ s₁.sp = s₂.sp

/-- `pbkG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem pbkImp (h : ∃ s, (Spec.Pbkdf2.pbkdf2Contract S W AArch64.abi 16).pre s) :
    (pbkG S W).Implies (Spec.Pbkdf2.pbkdf2Contract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, pbkG, stk, AArch64.abi, AArch64.argRegs] using h

end VG.Proof.Pbkdf2.Md.AArch64
