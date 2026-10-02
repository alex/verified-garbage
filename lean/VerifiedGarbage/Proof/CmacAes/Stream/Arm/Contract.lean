import VerifiedGarbage.Proof.CmacAes.Arm.Verified
import VerifiedGarbage.Proof.Aes.Arm.ExpandKey
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Impl.CmacAes.Stream.Arm

/-!
# Streaming AES-CMAC on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/Contract.lean`, which imply these
(`Verified.lean`). `init` calls `vg_cmac_aes_subkeys`, whose frame uses the
8 bytes below the stack pointer; `absorb` and `finish` push the two stack
arguments of `vg_cmac_aes_update` and `vg_cmac_aes_finalize` below the
stack pointer, and those functions' frames use the 8 bytes below that: so
the 8 or 16 bytes below the stack pointer may not overlap any buffer.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm

/-- `vg_cmac_aes_init(state = r0, key = r1, key_len = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 304⟩
    let key : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2304⟩
    let blw : Region := ⟨State.addr s.sp - 8, 8⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint key ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 304 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2304 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r2).toNat = 16 ∨ (s.gpr .r2).toNat = 24 ∨ (s.gpr .r2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (State.addr (s.gpr .r0))
      (Spec.Aes.bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) []
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3

/-- `count`, in `r2:r3` (AAPCS: the low word in `r2`). -/
def countArm (s : State) : BitVec 64 := s.gpr .r3 ++ s.gpr .r2

/-- `vg_cmac_aes_absorb(state = r0, rounds = r1, count = r2:r3, data = [sp], len = [sp, #4], scratch = [sp, #8])`. -/
def absorbArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 304⟩
    let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
    let scr : Region := ⟨State.addr (stackArg s 2), 2304⟩
    let args : Region := ⟨stackArgAddr s 0, 12⟩
    let blw : Region := ⟨State.addr s.sp - 16, 16⟩
    s.rd = [data, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint data ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 304 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 2304 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 12 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (State.addr (s.gpr .r0)) key msg →
      (s.gpr .r1).toNat = Spec.Aes.rounds (key.length / 4) →
      countArm s = BitVec.ofNat 64 msg.length → msg.length + (stackArg s 1).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (State.addr (s.gpr .r0)) key
        (msg ++ Spec.Aes.bytesAt s.mem (State.addr (stackArg s 0)) (stackArg s 1).toNat)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧
      stackArg s₁ 2 = stackArg s₂ 2

/-- `vg_cmac_aes_finish(state = r0, rounds = r1, count = r2:r3, out = [sp], scratch = [sp, #4])`. -/
def finishArm : Contract isa where
  pre s :=
    let state : Region := ⟨State.addr (s.gpr .r0), 304⟩
    let out : Region := ⟨State.addr (stackArg s 0), 16⟩
    let scr : Region := ⟨State.addr (stackArg s 1), 2304⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    let blw : Region := ⟨State.addr s.sp - 16, 16⟩
    s.rd = [args] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scr ∧
      blw.Disjoint state ∧ blw.Disjoint out ∧ blw.Disjoint scr ∧
      (s.gpr .r0).toNat + 304 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 16 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 2304 ≤ 2 ^ 32 ∧ 16 ≤ s.sp.toNat ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
      ((s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (State.addr (s.gpr .r0)) key msg →
      (s.gpr .r1).toNat = Spec.Aes.rounds (key.length / 4) →
      countArm s = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (State.addr (stackArg s 0)) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
      s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1

end VG.Proof.CmacAes.Stream.Arm
