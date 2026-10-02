import VerifiedGarbage.Impl.CmacTripleDes.X86
import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.TCB.X86.Target

/-!
# TDEA-CMAC on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/TripleDesContract.lean`, which imply these
(`Implies.lean`). The arguments are on the stack, from `[esp + 4]` (cdecl);
the functions call nothing and use no stack.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86

/-- `CIPH_K` for TDEA with the key schedule at `w`, in `m`. -/
abbrev ciphAt (m : Mem) (w : Addr) : Spec.Cmac.Cipher := Spec.Cmac.tdesWith (Spec.TripleDes.scheduleAt m w)

/-- `vg_cmac_triple_des_init(key, key_len, out, scratch)`. -/
def initX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
    let out : Region := ⟨(arg s 2).setWidth 64, 400⟩
    let scr : Region := ⟨(arg s 3).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, args] ∧ s.wr = [out, scr] ∧ key.Disjoint out ∧ key.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint out ∧ args.Disjoint scr ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 400 ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 640 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      Spec.TripleDes.validKey (arg s 1).toNat
  post s s' :=
    let k := Spec.TripleDes.expandKey (Spec.TripleDes.bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
    let ks := Spec.Cmac.subkeys (Spec.Cmac.tdesWith k) 8
    Spec.TripleDes.scheduleAt s'.mem ((arg s 2).setWidth 64) = k ∧
      Spec.Aes.bytesAt s'.mem ((arg s 2).setWidth 64 + 384) 16 = ks.1 ++ ks.2
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `vg_cmac_triple_des_update(schedule, state, data, n, scratch)`. -/
def updateX86 : Contract isa where
  pre s :=
    let sched : Region := ⟨(arg s 0).setWidth 64, 384⟩
    let state : Region := ⟨(arg s 1).setWidth 64, 8⟩
    let data : Region := ⟨(arg s 2).setWidth 64, 8 * (arg s 3).toNat⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [sched, data, args] ∧ s.wr = [state, scr] ∧
      sched.Disjoint state ∧ sched.Disjoint scr ∧ data.Disjoint state ∧ data.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (arg s 0).toNat + 384 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + 8 * (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 640 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' :=
    Spec.Aes.bytesAt s'.mem ((arg s 1).setWidth 64) 8 =
      Spec.Cmac.chain (ciphAt s.mem ((arg s 0).setWidth 64)) (Spec.Aes.bytesAt s.mem ((arg s 1).setWidth 64) 8)
        (Spec.Cmac.blocksAt s.mem ((arg s 2).setWidth 64) 8 (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

/-- `vg_cmac_triple_des_finalize(key, state, last, last_len, scratch)`. -/
def finalizeX86 : Contract isa where
  pre s :=
    let key : Region := ⟨(arg s 0).setWidth 64, 400⟩
    let state : Region := ⟨(arg s 1).setWidth 64, 8⟩
    let last : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scr : Region := ⟨(arg s 4).setWidth 64, 640⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [key, last, args] ∧ s.wr = [state, scr] ∧
      key.Disjoint state ∧ key.Disjoint scr ∧ last.Disjoint state ∧ last.Disjoint scr ∧
      state.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧ ret.Disjoint state ∧ ret.Disjoint scr ∧
      (arg s 0).toNat + 400 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 8 ≤ 2 ^ 32 ∧
      (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 640 ≤ 2 ^ 32 ∧
      (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 ∧ (arg s 3).toNat ≤ 8
  post s s' :=
    let ciph := ciphAt s.mem ((arg s 0).setWidth 64)
    let ks := Spec.Cmac.subkeys ciph 8
    Spec.Aes.bytesAt s.mem ((arg s 0).setWidth 64 + 384) 16 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 8 = 0 → (msg = [] ∨ 0 < (arg s 3).toNat) →
      Spec.Aes.bytesAt s.mem ((arg s 1).setWidth 64) 8 =
        Spec.Cmac.chain ciph (Spec.Cmac.zeros 8) (Spec.Cmac.blocks 8 msg) →
      Spec.Aes.bytesAt s'.mem ((arg s 1).setWidth 64) 8 =
        Spec.Cmac.macFull ciph 8 (msg ++ Spec.Aes.bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.CmacTripleDes.X86
