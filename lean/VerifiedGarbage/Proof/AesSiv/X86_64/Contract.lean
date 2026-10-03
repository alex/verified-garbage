import VerifiedGarbage.Proof.CmacAes.Stream.X86_64.Call
import VerifiedGarbage.Impl.AesSiv.X86_64
import VerifiedGarbage.Spec.Siv

/-!
# AES-SIV on x86-64: the contracts the proofs are written against

The artifacts' contracts are the shared ones of `Spec/Siv/Contract.lean`,
which imply these (`Verified.lean`). Each function calls functions that call
`vg_aes_ctr32`: the two return addresses are in the 16 bytes
below the stack pointer, which may not overlap any buffer. `open`'s contract
lets it leak whether the IV is right; this one does not (the code masks the
data without a branch), which the shared contract implies.
-/

namespace VG.Proof.AesSiv.X86_64

open VG VG.X86_64

/-- `vg_aes_siv_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 512⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧
      stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 512 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 32 ∨ (s.gpr .rsi).toNat = 48 ∨ (s.gpr .rsi).toNat = 64)
  post s s' :=
    Spec.Siv.KeyRepr s'.mem (s.gpr .rdx) (Spec.Aes.bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- `vg_aes_siv_s2v_start(ctx = rdi, rounds = rsi, d = rdx, scratch = rcx)`. -/
def s2vStartX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 512⟩
    let d : Region := ⟨s.gpr .rdx, 16⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [ctx] ∧ s.wr = [d, scr] ∧
      ctx.Disjoint d ∧ ctx.Disjoint scr ∧ d.Disjoint scr ∧
      ret.Disjoint ctx ∧ ret.Disjoint d ∧ ret.Disjoint scr ∧
      stack.Disjoint ctx ∧ stack.Disjoint d ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 512 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Siv.s2vStart (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx

/-- `vg_aes_siv_s2v_ad(ctx = rdi, rounds = rsi, d = rdx, data = rcx, len = r8, scratch = r9)`. -/
def s2vAdX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 512⟩
    let d : Region := ⟨s.gpr .rdx, 16⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2560⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack := below (s.gpr .rsp) 16
    16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [ctx, data] ∧ s.wr = [d, scr] ∧
      ctx.Disjoint d ∧ ctx.Disjoint scr ∧ data.Disjoint d ∧ data.Disjoint scr ∧ d.Disjoint scr ∧
      ret.Disjoint ctx ∧ ret.Disjoint data ∧ ret.Disjoint d ∧ ret.Disjoint scr ∧
      stack.Disjoint ctx ∧ stack.Disjoint data ∧ stack.Disjoint d ∧ stack.Disjoint scr ∧
      (s.gpr .rdi).toNat + 512 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)
  post s s' :=
    Spec.Aes.bytesAt s'.mem (s.gpr .rdx) 16 =
      Spec.Siv.s2vStep (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16) (Spec.Aes.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub s₁ s₂ :=
    s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
      s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
      s₁.gpr .r9 = s₂.gpr .r9

/-- The precondition of `vg_aes_siv_seal` and `vg_aes_siv_open`
`(ctx = rdi, rounds = rsi, d = rdx, data = rcx, len = r8, work = r9)`. -/
def cryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 512⟩
  let d : Region := ⟨s.gpr .rdx, 16⟩
  let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
  let work : Region := ⟨s.gpr .r9, 2560⟩
  let ret : Region := ⟨s.gpr .rsp, 8⟩
  let stack := below (s.gpr .rsp) 16
  16 ≤ (s.gpr .rsp).toNat ∧ s.rd = [ctx, d] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ d.Disjoint data ∧ d.Disjoint work ∧ data.Disjoint work ∧
    ret.Disjoint ctx ∧ ret.Disjoint d ∧ ret.Disjoint data ∧ ret.Disjoint work ∧
    stack.Disjoint ctx ∧ stack.Disjoint d ∧ stack.Disjoint data ∧ stack.Disjoint work ∧
    (s.gpr .rdi).toNat + 512 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64 ∧
    ((s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14)

/-- The public arguments of `vg_aes_siv_seal` and `vg_aes_siv_open`. -/
def cryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rsp = s₂.gpr .rsp ∧ s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧
    s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧
    s₁.gpr .r9 = s₂.gpr .r9

/-- `vg_aes_siv_seal(ctx = rdi, rounds = rsi, d = rdx, data = rcx, len = r8, work = r9)`. -/
def sealX86_64 : Contract isa where
  pre := cryptPre
  post s s' :=
    Spec.Siv.sealWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16)
        (Spec.Aes.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) =
      (Spec.Aes.bytesAt s'.mem (s.gpr .r9) 16, Spec.Aes.bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  pub := cryptPub

/-- `vg_aes_siv_open`, with the same arguments. -/
def openX86_64 : Contract isa where
  pre := cryptPre
  post s s' :=
    match Spec.Siv.openWith (Spec.Siv.ctxMac s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
        (Spec.Siv.ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (Spec.Aes.bytesAt s.mem (s.gpr .rdx) 16)
        (Spec.Aes.bytesAt s.mem (s.gpr .r9) 16) (Spec.Aes.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ Spec.Aes.bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        Spec.Aes.bytesAt s'.mem (s.gpr .rcx) (s.gpr .r8).toNat = Spec.Siv.zeros (s.gpr .r8).toNat
  pub := cryptPub

end VG.Proof.AesSiv.X86_64
