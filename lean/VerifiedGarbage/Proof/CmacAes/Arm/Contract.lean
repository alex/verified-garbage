import VerifiedGarbage.Proof.CmacAes.Arm.Call

/-!
# AES-CMAC on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/Contract.lean`, which imply these
(`Verified.lean`). Each function pushes `vg_aes_ctr32`'s two stack arguments
in the 8 bytes below the stack pointer, which may not overlap any buffer.
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule = r0, rounds = r1, state = r2, data = r3, n = [sp], scratch = [sp + 4])`. -/
def updateArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let data : Region := ⟨State.addr (s.gpr .r3), 16 * (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint sched ∧ below.Disjoint data ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 16 * (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
      Spec.Cmac.chain (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
        (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16)
        (Spec.Cmac.blocksAt s.mem (State.addr (s.gpr .r3)) 16 (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

/-- `vg_cmac_aes_subkeys(schedule = r0, rounds = r1, subkeys = r2, scratch = r3)`. -/
def subkeysArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 240⟩
    let subk : Region := ⟨State.addr (s.gpr .r2), 32⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2176⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      below.Disjoint sched ∧ below.Disjoint subk ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 240 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 32 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2176 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) 16
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_cmac_aes_finalize(key = r0, rounds = r1, state = r2, last = r3, last_len = [sp], scratch = [sp + 4])`. -/
def finalizeArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 272⟩
    let state : Region := ⟨State.addr (s.gpr .r2), 16⟩
    let last : Region := ⟨State.addr (s.gpr .r3), (stackArg s 0).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2176⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let below : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      below.Disjoint key ∧ below.Disjoint last ∧ below.Disjoint state ∧ below.Disjoint scr ∧
      (s.gpr .r0).toNat + 272 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 16 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + (stackArg s 0).toNat ≤ 2 ^ 32 ∧ (stackArg s 1).toNat + 2176 ≤ 2 ^ 32 ∧
      8 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14) ∧
      (stackArg s 0).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0) + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (stackArg s 0).toNat) →
      Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2)) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r3)) (stackArg s 0).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacAes.Arm
