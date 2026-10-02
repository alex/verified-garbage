import VerifiedGarbage.Proof.CmacAes.AArch64.Verified
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Impl.CmacAes.Stream.AArch64

/-!
# Streaming AES-CMAC on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/Contract.lean`, which imply these
(`Verified.lean`). A call (`bl`) stores nothing in memory, so no stack is
used.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64

/-- `vg_cmac_aes_init(state = x0, key = x1, key_len = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 304⟩
    let key : Region := ⟨s.gpr .x1, (s.gpr .x2).toNat⟩
    let scr : Region := ⟨s.gpr .x3, 2304⟩
    s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      (s.gpr .x0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + (s.gpr .x2).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .x2).toNat = 16 ∨ (s.gpr .x2).toNat = 24 ∨ (s.gpr .x2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (s.gpr .x0) (Spec.Aes.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_absorb(state = x0, rounds = x1, count = x2, data = x3, len = x4, scratch = x5)`. -/
def absorbAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 304⟩
    let data : Region := ⟨s.gpr .x3, (s.gpr .x4).toNat⟩
    let scr : Region := ⟨s.gpr .x5, 2304⟩
    s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      (s.gpr .x0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + (s.gpr .x4).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x5).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .x0) key msg →
      (s.gpr .x1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .x2 = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .x4).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (s.gpr .x0) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.gpr .x5 = s₂.gpr .x5 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_aes_finish(state = x0, rounds = x1, count = x2, out = x3, scratch = x4)`. -/
def finishAArch64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .x0, 304⟩
    let out : Region := ⟨s.gpr .x3, 16⟩
    let scr : Region := ⟨s.gpr .x4, 2304⟩
    s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .x0).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .x3).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .x1).toNat = 10 ∨ (s.gpr .x1).toNat = 12 ∨ (s.gpr .x1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .x0) key msg →
      (s.gpr .x1).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .x2 = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .x3) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacAes.Stream.AArch64
