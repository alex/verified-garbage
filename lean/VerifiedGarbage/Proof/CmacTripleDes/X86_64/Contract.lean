import VerifiedGarbage.Impl.CmacTripleDes.X86_64
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.Framework.X86_64.Abi

/-!
# TDEA-CMAC on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/TripleDesContract.lean`, which imply these
(`Verified.lean`). The functions call nothing and use no stack.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key = rdi, key_len = rsi, out = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let out : Region := ⟨s.gpr .rdx, 400⟩
    let scr : Region := ⟨s.gpr .rcx, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint out ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 400 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 640 ≤ 2 ^ 64 ∧ Spec.TripleDes.validKey (s.gpr .rsi).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem (s.gpr .rdx) = k ∧
      Spec.Aes.bytesAt s'.mem (s.gpr .rdx + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_update(schedule = rdi, state = rsi, data = rdx, n = rcx, scratch = r8)`. -/
def updateX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 384⟩
    let state : Region := ⟨s.gpr .rsi, 8⟩
    let data : Region := ⟨s.gpr .rdx, 8 * (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 8 * (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 640 ≤ 2 ^ 64
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .rdi)) (Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8)
        (Spec.Cmac.blocksAt s.mem (s.gpr .rdx) 8 (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_triple_des_finalize(key = rdi, state = rsi, last = rdx, last_len = rcx, scratch = r8)`. -/
def finalizeX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 400⟩
    let state : Region := ⟨s.gpr .rsi, 8⟩
    let last : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scr : Region := ⟨s.gpr .r8, 640⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (s.gpr .rdi).toNat + 400 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + 8 ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 640 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat ≤ 8
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .rdi)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem (s.gpr .rdi + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (s.gpr .rcx).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .rsi) 8 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .rsi) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.CmacTripleDes.X86_64
