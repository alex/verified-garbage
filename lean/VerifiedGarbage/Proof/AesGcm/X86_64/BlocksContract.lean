import VerifiedGarbage.Proof.AesGcm.X86_64.Contract

/-!
# AES-GCM on whole blocks, x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. `vg_aes_gcm_encrypt_blocks`
and `vg_aes_gcm_decrypt_blocks` `(ctx = rdi, rounds = rsi, counter = rdx,
y = rcx, data = r8, n = r9, scratch = [rsp + 8])`; the shared contracts of
`Spec/Gcm/Contract.lean` imply these, with 64 bytes of stack
(`BlocksVerified.lean`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Gcm (Block blockAt blocksAt ctxCiph ctxH ctr32 ghashFrom inc32)

/-- The stack they use: their frame of the arguments (56 bytes) and the
return address of a call. -/
abbrev stk64 (s : State) : Region := below (s.gpr .rsp) 64

/-- What both need. -/
def blocksPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let ctr : Region := ⟨s.gpr .rdx, 16⟩
  let y : Region := ⟨s.gpr .rcx, 16⟩
  let data : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat * 16⟩
  let scr : Region := ⟨arg s 0, 2048⟩
  s.rd = [ctx, args s 1] ∧ s.wr = [ctr, y, data, scr] ∧
    ctx.Disjoint ctr ∧ ctx.Disjoint y ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    ctr.Disjoint y ∧ ctr.Disjoint data ∧ ctr.Disjoint scr ∧ ctr.Disjoint (args s 1) ∧
    y.Disjoint data ∧ y.Disjoint scr ∧ y.Disjoint (args s 1) ∧
    data.Disjoint scr ∧ data.Disjoint (args s 1) ∧ scr.Disjoint (args s 1) ∧
    (ret s).Disjoint ctr ∧ (ret s).Disjoint y ∧ (ret s).Disjoint data ∧ (ret s).Disjoint scr ∧
    (stk64 s).Disjoint ctx ∧ (stk64 s).Disjoint ctr ∧ (stk64 s).Disjoint y ∧ (stk64 s).Disjoint data ∧
    (stk64 s).Disjoint scr ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 16 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 16 ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat * 16 ≤ 2 ^ 64 ∧ (arg s 0).toNat + 2048 ≤ 2 ^ 64 ∧
    64 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ rounds s

def blocksPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0

/-- `vg_aes_gcm_encrypt_blocks`. -/
def encryptBlocksX86_64 : Contract isa where
  pre := blocksPre
  post s s' :=
    let n := (s.gpr .r9).toNat
    let c := ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx))
      (blocksAt s.mem (s.gpr .r8) n)
    blocksAt s'.mem (s.gpr .r8) n = c ∧ blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
      blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c
  pub := blocksPub

/-- `vg_aes_gcm_decrypt_blocks`. -/
def decryptBlocksX86_64 : Contract isa where
  pre := blocksPre
  post s s' :=
    let n := (s.gpr .r9).toNat
    let c := blocksAt s.mem (s.gpr .r8) n
    blocksAt s'.mem (s.gpr .r8) n =
        ctr32 (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (blockAt s.mem (s.gpr .rdx)) c ∧
      blockAt s'.mem (s.gpr .rdx) = Nat.repeat inc32 n (blockAt s.mem (s.gpr .rdx)) ∧
      blockAt s'.mem (s.gpr .rcx) = ghashFrom (ctxH s.mem (s.gpr .rdi)) (blockAt s.mem (s.gpr .rcx)) c
  pub := blocksPub

end VG.Proof.AesGcm
