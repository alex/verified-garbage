import VerifiedGarbage.Impl.CmacTripleDes.Arm
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.TCB.Arm.Target

/-!
# TDEA-CMAC on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/TripleDesContract.lean`, which imply these
(`Implies.lean`). The functions call nothing and use no stack; `update` and
`finalize` take `scratch` on the stack.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key = r0, key_len = r1, out = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let out : Region := ⟨State.addr (s.gpr .r2), 400⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 640⟩
    s.rd = [key] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 400 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 640 ≤ 2 ^ 32 ∧ Spec.TripleDes.validKey (s.gpr .r1).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (State.addr (s.gpr .r2)) = k ∧
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r2) + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_cmac_triple_des_update(schedule = r0, state = r1, data = r2, n = r3, scratch = [sp])`. -/
def updateArm : Contract isa where
  pre s :=
    let sched : Region := ⟨State.addr (s.gpr .r0), 384⟩
    let state : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let data : Region := ⟨State.addr (s.gpr .r2), 8 * (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧ (s.gpr .r0).toNat + 384 ≤ 2 ^ 32 ∧
      (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 8 * (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
      (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) 8 =
      Spec.Cmac.chain (ciphAt s.mem (State.addr (s.gpr .r0))) (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8)
        (Spec.Cmac.blocksAt s.mem (State.addr (s.gpr .r2)) 8 (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

/-- `vg_cmac_triple_des_finalize(key = r0, state = r1, last = r2, last_len = r3, scratch = [sp])`. -/
def finalizeArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), 400⟩
    let state : Region := ⟨State.addr (s.gpr .r1), 8⟩
    let last : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 0), 640⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ state.Disjoint args ∧ scr.Disjoint args ∧
      (s.gpr .r0).toNat + 400 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 8 ≤ 2 ^ 32 ∧
      (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 640 ≤ 2 ^ 32 ∧
      s.sp.toNat + 4 ≤ 2 ^ 32 ∧ (s.gpr .r3).toNat ≤ 8
  post s s' :=
    let ciph := ciphAt s.mem (State.addr (s.gpr .r0))
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r0) + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (s.gpr .r3).toNat) →
      Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) 8 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (State.addr (s.gpr .r1)) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.CmacTripleDes.Arm
