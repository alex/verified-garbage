import VerifiedGarbage.Proof.CmacAes.X86_64.Verified
import VerifiedGarbage.Proof.Cmac.Stream
import VerifiedGarbage.Impl.CmacAes.Stream.X86_64

/-!
# Streaming AES-CMAC on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Cmac/Contract.lean`,
which imply these (`Verified.lean`). Each function calls functions that call
`vg_aes_ctr32`: the two return addresses are in the 16 bytes below the stack
pointer, which may not overlap any buffer.
-/

namespace VG.Proof.CmacAes.Stream.X86_64

open VG VG.X86_64

/-- `vg_cmac_aes_init(state = rdi, key = rsi, key_len = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let key : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let scr : Region := ⟨s.gpr .rcx, 2304⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [key] ∧ s.wr = [state, scr] ∧
      state.Disjoint key ∧ state.Disjoint scr ∧ key.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint key ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint key ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .rdx).toNat = 16 ∨ (s.gpr .rdx).toNat = 24 ∨ (s.gpr .rdx).toNat = 32)
  post s s' :=
    Spec.Cmac.Repr s'.mem (s.gpr .rdi) (Spec.Aes.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) []
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- `vg_cmac_aes_absorb(state = rdi, rounds = rsi, count = rdx, data = rcx, len = r8, scratch = r9)`. -/
def absorbX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2304⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [data] ∧ s.wr = [state, scr] ∧
      state.Disjoint data ∧ state.Disjoint scr ∧ data.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .r9).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .rdi) key msg →
      (s.gpr .rsi).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .rdx = BitVec.ofNat 64 msg.length → msg.length + (s.gpr .r8).toNat < 2 ^ 64 →
      Spec.Cmac.Repr s'.mem (s.gpr .rdi) key
        (msg ++ Spec.Aes.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9

/-- `vg_cmac_aes_finish(state = rdi, rounds = rsi, count = rdx, out = rcx, scratch = r8)`. -/
def finishX86_64 : Contract isa where
  pre s :=
    let state : Region := ⟨s.gpr .rdi, 304⟩
    let out : Region := ⟨s.gpr .rcx, 16⟩
    let scr : Region := ⟨s.gpr .r8, 2304⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [] ∧ s.wr = [state, out, scr] ∧
      state.Disjoint out ∧ state.Disjoint scr ∧ out.Disjoint scr ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scr ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 304 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + 2304 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    ∀ key msg, Spec.Cmac.Repr s.mem (s.gpr .rdi) key msg →
      (s.gpr .rsi).toNat = Spec.Aes.rounds (key.length / 4) →
      s.gpr .rdx = BitVec.ofNat 64 msg.length → msg.length < 2 ^ 64 →
      Spec.Aes.bytesAt s'.mem (s.gpr .rcx) 16 = Spec.Cmac.aesCmac key 16 msg
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8

end VG.Proof.CmacAes.Stream.X86_64
