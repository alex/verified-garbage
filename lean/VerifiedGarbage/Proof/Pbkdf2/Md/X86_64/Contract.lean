import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Calls

/-!
# HMAC and PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: the shared contracts

`pbkG` is the contract the proof of `pbkdf2` is written against:
`VG.Spec.Pbkdf2.pbkdf2Contract` with its facts spelt out, which it implies for
any streaming hash function and scratch space (`generic_implies`), as HMAC's
`initG` and `finG` (`Calls.lean`) imply `VG.Spec.Hmac.initContract` and
`VG.Spec.Hmac.finalizeContract` (`initImp`, `finImp`). `initSat` and `finSat`
are states satisfying HMAC's shared contracts' preconditions, from which each
hash function's instance shows them satisfiable.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64

open VG.X86_64
open VG.Proof.Pbkdf2.Md.X86_64.Calls (initG finG)
open Spec.Hmac (StreamingHash)
open Spec.Sha256 (bytesAt)

variable (S : StreamingHash) (W : Nat)

/-- `pbkdf2(password, password_len, salt, salt_len, c, out, out_len, scratch)`,
with `8 W` bytes of scratch space and three calls below it. -/
def pbkG : Contract isa where
  pre s :=
    let outLen := stackArg s 0
    let sc := stackArg s 1
    let pw : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let salt : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let out : Region := ⟨s.gpr .r9, outLen.toNat⟩
    let scratch : Region := ⟨sc, W * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - BitVec.ofNat 64 24, 24⟩
    24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧
    s.rd = [pw, salt, args] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    ret.Disjoint pw ∧ ret.Disjoint salt ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧ ret.Disjoint args ∧
    stack.Disjoint pw ∧ stack.Disjoint salt ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    stack.Disjoint args ∧
    (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + outLen.toNat ≤ 2 ^ 64 ∧ sc.toNat + W * 8 ≤ 2 ^ 64 ∧
    0 < ((s.gpr .r8).setWidth 32).toNat ∧ outLen.toNat ≤ (2 ^ 32 - 1) * S.digestBytes
  post s s' :=
    let outLen := stackArg s 0
    Spec.Pbkdf2.pbkdf2Hmac S (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
      (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) ((s.gpr .r8).setWidth 32).toNat outLen.toNat =
      some (bytesAt s'.mem (s.gpr .r9) outLen.toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ (s₁.gpr .r8).setWidth 32 = (s₂.gpr .r8).setWidth 32 ∧
    s₁.gpr .r9 = s₂.gpr .r9 ∧
    stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧
    s₁.gpr .rsp = s₂.gpr .rsp

theorem map_range2 {α : Type} (f : Nat → α) : List.map f (List.range 2) = [f 0, f 1] := rfl

/-- `pbkG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem pbkImp (h : ∃ s, (Spec.Pbkdf2.pbkdf2Contract S W X86_64.abi 24).pre s) :
    (pbkG S W).Implies (Spec.Pbkdf2.pbkdf2Contract S W X86_64.abi 24) := by
  exact
    { pre := by
        intro s h
        -- Twice: the stack arguments' list evaluates only on the second pass.
        sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, pbkG, X86_64.abi, X86_64.argRegs, map_range2, List.append_eq] at h
        sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, pbkG, X86_64.abi, X86_64.argRegs, map_range2, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, pbkG, X86_64.abi, X86_64.argRegs, map_range2, List.append_eq]
        sig_and_intros
        sig_close
        all_goals with_reducible assumption
      post := by
        rintro s s' - h
        sig_post [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, pbkG, X86_64.abi, X86_64.argRegs, map_range2, List.append_eq]
        sig_reduce [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, pbkG, X86_64.abi, X86_64.argRegs, map_range2, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, pbkG, X86_64.abi, X86_64.argRegs, map_range2, List.append_eq] at h
        simp only [List.getD_cons_succ, List.getD_cons_zero] at h
        sig_split h
        rename_i h1 h2 h3 h4 h5 h6 h7 h8
        exact ⟨h2, h3, h4, h5, h6, h7, h8, h, h1⟩
      sat := h }

/-! ## HMAC's `init` and `finalize` -/

/-- A state satisfying `init`'s precondition, with states of `S` bytes and
`8 sc` bytes of scratch space (and a one-byte key). -/
def initSat (S sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rdx => 0x30000 | .rcx => 1 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x30000, 1⟩]
  wr := [⟨0x10000, S⟩, ⟨0x20000, S⟩, ⟨0x40000, 8 * sc⟩]

/-- A state satisfying `finalize`'s precondition, with states of `S` bytes,
a digest of `D` bytes and `8 sc` bytes of scratch space. -/
def finSat (S D sc : Nat) : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rsi => 0x20000 | .rcx => 0x30000 | .r8 => 0x40000
    | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x20000, S⟩]
  wr := [⟨0x10000, S⟩, ⟨0x30000, D⟩, ⟨0x40000, 8 * sc⟩]

/-- `initG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem initImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.initContract S W X86_64.abi 16).pre s) :
    (initG S W).Implies (Spec.Hmac.initContract S W X86_64.abi 16) := by
  generic_implies [
    Spec.Hmac.initContract, Spec.Hmac.initSig, initG, X86_64.abi, X86_64.argRegs] using h

/-- `finG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem finImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Hmac.finalizeContract S W X86_64.abi 16).pre s) :
    (finG S W).Implies (Spec.Hmac.finalizeContract S W X86_64.abi 16) := by
  generic_implies [
    Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, finG, X86_64.abi, X86_64.argRegs] using h

end VG.Proof.Pbkdf2.Md.X86_64
