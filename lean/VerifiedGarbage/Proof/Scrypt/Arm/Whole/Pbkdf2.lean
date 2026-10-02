import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Spec.Pbkdf2.Generic
import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.TCB.Arm.Target

/-!
# scrypt on 32-bit ARM: PBKDF2-HMAC-SHA256 as a callee

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Scrypt/AArch64/Whole/Pbkdf2.lean`): `vg_pbkdf2_hmac_sha256` is
verified against the shared contract `VG.Spec.Hmac.sha256I.pbkdf2Contract`;
its caller works with the same contract spelt out (`pbkA`): `pbk_correct`
and `pbk_ct` are its correctness and constant time under `pbkA`, from its
`Verified` proof.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG.Arm

/-- `pbkdf2(password = r0, password_len = r1, salt = r2, salt_len = r3, c,
out, out_len, scratch)`, the last four on the stack, with 1600 bytes of
scratch space and 24 bytes of stack below the stack pointer. -/
def pbkA : Contract isa where
  pre s :=
    let pw : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let salt : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let out : Region := ⟨State.addr (stackArg s 1), (stackArg s 2).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 3), 200 * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 16⟩
    let stk : Region := ⟨State.addr s.sp - BitVec.ofNat 64 24, 24⟩
    24 ≤ s.sp.toNat ∧ s.sp.toNat + 16 ≤ 2 ^ 32 ∧ s.rd = [pw, salt, args] ∧ s.wr = [out, scratch] ∧
    pw.Disjoint out ∧ pw.Disjoint scratch ∧ salt.Disjoint out ∧ salt.Disjoint scratch ∧
    out.Disjoint scratch ∧ out.Disjoint args ∧ scratch.Disjoint args ∧
    stk.Disjoint pw ∧ stk.Disjoint salt ∧ stk.Disjoint out ∧ stk.Disjoint scratch ∧ stk.Disjoint args ∧
    (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (stackArg s 1).toNat + (stackArg s 2).toNat ≤ 2 ^ 32 ∧ (stackArg s 3).toNat + 200 * 8 ≤ 2 ^ 32 ∧
    0 < (stackArg s 0).toNat ∧ (stackArg s 2).toNat ≤ (2 ^ 32 - 1) * 32
  post s s' :=
    Spec.Pbkdf2.pbkdf2Hmac Spec.Hmac.sha256S
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
      (Spec.Sha256.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) (stackArg s 0).toNat
      (stackArg s 2).toNat =
      some (Spec.Sha256.bytesAt s'.mem (State.addr (stackArg s 1)) (stackArg s 2).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
    stackArg s₁ 2 = stackArg s₂ 2 ∧ stackArg s₁ 3 = stackArg s₂ 3

theorem pbk_pre {s : State} (h : pbkA.pre s) :
    (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24).pre s := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pre [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  simp only [pbkA, State.addr] at h
  sig_split h
  sig_and_intros
  all_goals try simp only [State.addr]
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›
    | omega

theorem pbk_post {s s' : State} (h : (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24).post s s') :
    pbkA.post s s' := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch] at h
  sig_post [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at h
  exact h

theorem pbk_pub {s₁ s₂ : State} (h : pbkA.pub s₁ s₂) :
    (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24).pub s₁ s₂ := by
  simp only [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch]
  sig_pub [Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256I, Spec.Hmac.sha256S,
    Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact h

variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
include hv

theorem pbk_correct (s : State) (h : pbkA.pre s) :
    ∃ t s', Exec isa pbk s t s' ∧ abiPreserved s s' ∧ pbkA.post s s' := by
  obtain ⟨t, s', he, ha, hp⟩ := hv.1 s (pbk_pre h)
  exact ⟨t, s', he, ha, pbk_post hp⟩

theorem pbk_ct : ConstantTime isa pbkA.pre pbkA.pub pbk :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => hv.2.1 _ _ _ _ _ _ (pbk_pre h₁) (pbk_pre h₂) (pbk_pub hp) e₁ e₂

end VG.Proof.Scrypt.Arm.Whole
