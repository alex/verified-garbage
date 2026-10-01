import VerifiedGarbage.Proof.Cmac.Spec
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Impl.CmacAes.X86

/-!
# AES-CMAC on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/Contract.lean`, which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]` (cdecl).
Each call of `vg_aes_ctr32` pushes its six arguments and the return address
in the 28 bytes below `esp`, which may not overlap any buffer.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86

/-- `CIPH_K` for AES with the key schedule at `w` for `R` rounds, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) (R : Nat) : Spec.Cmac.Cipher :=
  Spec.Cmac.aesWith R (Spec.Aes.bytesAt m w (16 * (R + 1)))

/-- `vg_cmac_aes_update(schedule, rounds, state, data, n, scratch)`. -/
def updateX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let state : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let data : Region := ⟨(arg s 3).setWidth 64, 16 * (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint data ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 16 * (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) 16 =
      Spec.Cmac.chain (ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
        (Spec.Aes.bytesAt s.mem ((arg s 2).setWidth 64) 16)
        (Spec.Cmac.blocksAt s.mem ((arg s 3).setWidth 64) 16 (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

/-- `vg_cmac_aes_subkeys(schedule, rounds, subkeys, scratch)`. -/
def subkeysX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 240⟩
    let subk : Region := ⟨(arg s 2).setWidth 64, 32⟩
    let scr : Region := ⟨(arg s 3).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [sched, args] ∧ s.wr = [subk, scr] ∧
      sched.Disjoint subk ∧ sched.Disjoint scr ∧ subk.Disjoint scr ∧
      args.Disjoint subk ∧ args.Disjoint scr ∧ ret.Disjoint subk ∧ ret.Disjoint scr ∧
      stack.Disjoint sched ∧ stack.Disjoint subk ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 240 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 32 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 2176 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    let ks := Spec.Cmac.subkeys (ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) 16
    Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) 32 = ks.1 ++ ks.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `vg_cmac_aes_finalize(key, rounds, state, last, last_len, scratch)`. -/
def finalizeX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 272⟩
    let state : Region := ⟨(arg s 2).setWidth 64, 16⟩
    let last : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2176⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 28, 28⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint last ∧ stack.Disjoint state ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 272 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧ (arg s 5).toNat + 2176 ≤ 2 ^ 32 ∧
      28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14) ∧ (arg s 4).toNat ≤ 16
  post s s' :=
    let ciph := ciphAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < (arg s 4).toNat) →
      Spec.Aes.bytesAt s.mem ((arg s 2).setWidth 64) 16 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.CmacAes.X86
