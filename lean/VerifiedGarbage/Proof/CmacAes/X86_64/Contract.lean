import VerifiedGarbage.Proof.CmacAes.X86_64.Call
import VerifiedGarbage.Impl.CmacAes.X86_64

/-!
# AES-CMAC on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). Each function calls `vg_aes_ctr32`, whose
return address is in the 8 bytes below the stack pointer, which may not
overlap any buffer.
-/

namespace VG.Proof.CmacAes.X86_64

open VG VG.X86_64

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule = rdi, rounds = rsi, state = rdx, data = rcx, n = r8, scratch = r9)`. -/
def updateX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, 16 * (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched, data] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 * (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Cmac.chain (ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16)
        (Spec.Cmac.blocksAt s.mem (s.gpr .rcx) 16 (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_aes_subkeys(schedule = rdi, rounds = rsi, subkeys = rdx, scratch = rcx)`. -/
def subkeysX86_64 : Contract isa where
  pre s :=
    let sched : Region := ⟨s.gpr .rdi, 240⟩
    let subk : Region := ⟨s.gpr .rdx, 32⟩
    let scr : Region := ⟨s.gpr .rcx, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [sched] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      ret.Disjoint subk ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint subk ∧ stack.Disjoint scr ∧
      (s.gpr .rdx).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) 16
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 32 = ks.1 ++ ks.2
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_cmac_aes_finalize(key = rdi, rounds = rsi, state = rdx, last = rcx, last_len = r8, scratch = r9)`. -/
def finalizeX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, 272⟩
    let state : Region := ⟨s.gpr .rdx, 16⟩
    let last : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2176⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 8
    s.rd = [key, last] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint last ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 272 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2176 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14) ∧
      (s.gpr .r8).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (s.gpr .rdi + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (s.gpr .r8).toNat) →
      Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
      s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
      s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.CmacAes.X86_64
