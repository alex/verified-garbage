import VerifiedGarbage.Impl.CmacTripleDes.AArch64
import VerifiedGarbage.Spec.Cmac.TripleDesContract

/-!
# TDEA-CMAC on AArch64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/TripleDesContract.lean`, which imply these
(`Verified.lean`). The functions call nothing and use no stack: the return address stays in `x30`.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key = x0, key_len = x1, out = x2, scratch = x3)`. -/
def initAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, (s.gpr .x1).toNat⟩
    let out : Region := ⟨s.gpr .x2, 400⟩
    let scr : Region := ⟨s.gpr .x3, 640⟩
    s.rd = [key] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      (s.gpr .x0).toNat + (s.gpr .x1).toNat ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 400 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .x1).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .x0) (s.gpr .x1).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .x2) = k ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .x2 + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_update(schedule = x0, state = x1, data = x2, n = x3, scratch = x4)`. -/
def updateAArch64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .x0, 384⟩
    let state : Region := ⟨s.gpr .x1, 8⟩
    let data : Region := ⟨s.gpr .x2, 8 * (s.gpr .x3).toNat⟩
    let scr : Region := ⟨s.gpr .x4, 640⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 8 * (s.gpr .x3).toNat ≤ 2 ^ 64 ∧
      (s.gpr .x4).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .x0)) (Spec.Aes.bytesAt s.mem (s.gpr .x1) 8)
        (Spec.Cmac.blocksAt s.mem (s.gpr .x2) 8 (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

/-- `vg_cmac_triple_des_finalize(key = x0, state = x1, last = x2, last_len = x3, scratch = x4)`. -/
def finalizeAArch64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .x0, 400⟩
    let state : Region := ⟨s.gpr .x1, 8⟩
    let last : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scr : Region := ⟨s.gpr .x4, 640⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧
      (s.gpr .x0).toNat + 400 ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .x2).toNat + (s.gpr .x3).toNat ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + 640 ≤ 2 ^ 64 ∧
      (s.gpr .x3).toNat ≤ 8
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .x0)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (s.gpr .x0 + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (s.gpr .x3).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .x1) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .x1) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
      s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.CmacTripleDes.AArch64
