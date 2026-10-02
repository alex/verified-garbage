import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Calls

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: the shared contracts

`pbkG` is the contract the proof of `pbkdf2` is written against:
`VG.Spec.Pbkdf2.pbkdf2Contract` with its facts spelt out, which it implies for
any streaming hash function and scratch space (`generic_implies`). Every
argument is in a register, and the functions `pbkdf2` calls may use the 16
bytes below the stack pointer. Likewise HMAC's `initG` and `finG`
(`Calls.lean`) imply `VG.Spec.Hmac.initContract` and
`VG.Spec.Hmac.finalizeContract` (`initImp`, `finImp`); `initSat` and `finSat`
are states satisfying those contracts' preconditions, from which each hash
function's instance shows them satisfiable.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64

open VG.AArch64
open VG.Proof.Pbkdf2.Md.AArch64.Calls (stk initG finG)
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

/-! ## HMAC's `init` and `finalize` -/

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x2 => 0x30000 | .x3 => 1 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩, ⟨0x40000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x1 => 0x20000 | .x3 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-- `initG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem initImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.initContract S W AArch64.abi 16).pre s) :
    (initG S W).Implies (Spec.Hmac.initContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Hmac.initContract, Spec.Hmac.initSig, initG, stk, AArch64.abi, AArch64.argRegs] using h

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeContract S W AArch64.abi 16).pre s) :
    (finG S W).Implies (Spec.Hmac.finalizeContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, finG, stk, AArch64.abi, AArch64.argRegs] using h

end VG.Proof.Pbkdf2.Md.AArch64
