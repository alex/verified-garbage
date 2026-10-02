import VerifiedGarbage.Proof.CmacAes.X86.Verified
import VerifiedGarbage.Proof.Aes.X86.ExpandKey
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Impl.CmacAes.Stream.X86

/-!
# Streaming AES-CMAC on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Cmac/Contract.lean`, which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]` (cdecl);
`count` takes the slots 2 (low word) and 3. Each call of a CMAC function
pushes its six arguments and the return address in the 28 bytes below `esp`,
and the callee's call of `vg_aes_ctr32` uses 28 bytes below that: 56 bytes
(48 for `init`, whose calls take four arguments), which may not overlap any
buffer.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86

/-- The 64-bit `count` argument, in the slots 2 and 3 (low word first). -/
def countX86 (s : State) : BitVec 64 := arg s 3 ++ arg s 2

/-- `vg_cmac_aes_init(state, key, key_len, scratch)`. -/
def initX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 304⟩
    let key : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
    let scr : Region := ⟨(arg s 3).setWidth 64, 2304⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 48, 48⟩
    s.rd = [key, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint key ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 304 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 2304 ≤ 2 ^ 32 ∧ 48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
      ((arg s 2).toNat = 16 ∨ (arg s 2).toNat = 24 ∨ (arg s 2).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem ((arg s 0).setWidth 64) (Spec.Aes.bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

/-- `vg_cmac_aes_absorb(state, rounds, count, data, len, scratch)`. -/
def absorbX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 304⟩
    let data : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
    let scr : Region := ⟨(arg s 6).setWidth 64, 2304⟩
    let args : Region := ⟨argAddr s 0, 28⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 56, 56⟩
    s.rd = [data, args] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧ args.Disjoint state ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 304 ≤ 2 ^ 32 ∧ (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧
      (arg s 6).toNat + 2304 ≤ 2 ^ 32 ∧ 56 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 32 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem ((arg s 0).setWidth 64) key msg →
      (arg s 1).toNat = Spec.Aes.rounds (key.length / 4) →
      countX86 s = BitVec.ofNat 64 msg.length → msg.length + (arg s 5).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem ((arg s 0).setWidth 64) key
        (msg ++ Spec.Aes.bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 7, arg s₁ i = arg s₂ i

/-- `vg_cmac_aes_finish(state, rounds, count, out, scratch)`. -/
def finishX86 : Contract isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 304⟩
    let out : Region := ⟨(arg s 4).setWidth 64, 16⟩
    let scr : Region := ⟨(arg s 5).setWidth 64, 2304⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 56, 56⟩
    s.rd = [args] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (arg s 0).toNat + 304 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 16 ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 2304 ≤ 2 ^ 32 ∧ 56 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 ∧
      ((arg s 1).toNat = 10 ∨ (arg s 1).toNat = 12 ∨ (arg s 1).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem ((arg s 0).setWidth 64) key msg →
      (arg s 1).toNat = Spec.Aes.rounds (key.length / 4) →
      countX86 s = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem ((arg s 4).setWidth 64) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

end VG.Proof.CmacAes.Stream.X86
