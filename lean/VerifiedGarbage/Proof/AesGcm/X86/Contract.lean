import VerifiedGarbage.Spec.Gcm.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# AES-GCM on x86: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). The arguments are on the stack, from `[esp + 4]`
(cdecl), and may be overwritten (`writeArgs`); each call pushes its
arguments and the return address below `esp`: 28 bytes for
`vg_aes_ctr32`, 24 for `vg_ghash` (all `stream_init` and `stream_aad`
call), which no buffer overlaps, nor the return address.
-/

namespace VG.Proof.AesGcm.X86

open VG VG.X86
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- Whether the stack argument `i` holds 10, 12 or 14. -/
abbrev roundsOk (s : State) (i : Nat) : Prop :=
  (arg s i).toNat = 10 ∨ (arg s i).toNat = 12 ∨ (arg s i).toNat = 14

/-- All `n` stack arguments are public, and the stack pointer. -/
def pubN (n : Nat) (s₁ s₂ : State) : Prop := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_init(key, key_len, ctx, scratch)`. -/
def initPre (s : State) : Prop :=
  let key : Region := ⟨(arg s 0).setWidth 64, (arg s 1).toNat⟩
  let ctx : Region := ⟨(arg s 2).setWidth 64, 256⟩
  let scr : Region := ⟨(arg s 3).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 16⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [key] ∧ s.wr = [ctx, scr, args] ∧
  key.Disjoint ctx ∧ key.Disjoint scr ∧ key.Disjoint args ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧
  scr.Disjoint args ∧
  ret.Disjoint key ∧ ret.Disjoint ctx ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint key ∧ stack.Disjoint ctx ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 256 ≤ 2 ^ 32 ∧
  (arg s 3).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 ∧
  ((arg s 1).toNat = 16 ∨ (arg s 1).toNat = 24 ∨ (arg s 1).toNat = 32)

def initX86 : Contract isa where
  pre := initPre
  post s s' := KeyRepr s'.mem ((arg s 2).setWidth 64) (bytesAt s.mem ((arg s 0).setWidth 64) (arg s 1).toNat)
  pub := pubN 4

/-- `vg_aes_gcm_stream_init(ctx, nonce, nonce_len, state, scratch)`. -/
def streamInitPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(arg s 1).setWidth 64, (arg s 2).toNat⟩
  let st : Region := ⟨(arg s 3).setWidth 64, 80⟩
  let scr : Region := ⟨(arg s 4).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 20⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩
  s.rd = [ctx, nonce] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧
  nonce.Disjoint args ∧ st.Disjoint scr ∧ st.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint st ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint st ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 1).toNat + (arg s 2).toNat ≤ 2 ^ 32 ∧
  (arg s 3).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 24 ≤ 2 ^ 32

def streamInitX86 : Contract isa where
  pre := streamInitPre
  post s s' := ∀ ciph, StreamRepr s'.mem ((arg s 3).setWidth 64) ciph (ctxH s.mem ((arg s 0).setWidth 64))
    (bytesAt s.mem ((arg s 1).setWidth 64) (arg s 2).toNat) [] []
  pub := pubN 5

/-- `vg_aes_gcm_stream_aad(ctx, state, aad_len (2 words), data, len, scratch)`. -/
def streamAadPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 1).setWidth 64, 80⟩
  let data : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let scr : Region := ⟨(arg s 6).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 28⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 24, 24⟩
  s.rd = [ctx, data] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint data ∧ st.Disjoint scr ∧
  st.Disjoint args ∧ data.Disjoint scr ∧ data.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 80 ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 24 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 32 ≤ 2 ^ 32

def streamAadX86 : Contract isa where
  pre := streamAadPre
  post s s' := ∀ ciph iv a, StreamRepr s.mem ((arg s 1).setWidth 64) ciph (ctxH s.mem ((arg s 0).setWidth 64)) iv a [] →
    arg s 3 ++ arg s 2 = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem ((arg s 1).setWidth 64) ciph (ctxH s.mem ((arg s 0).setWidth 64)) iv
      (a ++ bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) []
  pub := pubN 7

/-- `vg_aes_gcm_stream_encrypt` and `_decrypt(ctx, rounds, state, aad_len, text_len, data, len, scratch)`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 2).setWidth 64, 80⟩
  let data : Region := ⟨(arg s 7).setWidth 64, (arg s 8).toNat⟩
  let scr : Region := ⟨(arg s 9).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 40⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx] ∧ s.wr = [st, data, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint data ∧
  st.Disjoint scr ∧ st.Disjoint args ∧ data.Disjoint scr ∧ data.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint data ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 80 ≤ 2 ^ 32 ∧
  (arg s 7).toNat + (arg s 8).toNat ≤ 2 ^ 32 ∧ (arg s 9).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧
  (s.gpr .esp).toNat + 44 ≤ 2 ^ 32 ∧ roundsOk s 1

def streamEncryptX86 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a p, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat)
      StreamRepr s'.mem ((arg s 2).setWidth 64) ciph h iv a c ∧
        bytesAt s'.mem ((arg s 7).setWidth 64) (arg s 8).toNat = c.drop p.length
  pub := pubN 10

def streamDecryptX86 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a c →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = c.length →
      let c' := c ++ bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat
      StreamRepr s'.mem ((arg s 2).setWidth 64) ciph h iv a c' ∧
        bytesAt s'.mem ((arg s 7).setWidth 64) (arg s 8).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := pubN 10

/-- `vg_aes_gcm_stream_finish(ctx, rounds, state, aad_len, text_len, work)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 2).setWidth 64, 80⟩
  let scr : Region := ⟨(arg s 7).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 32⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint scr ∧ st.Disjoint args ∧
  scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 80 ≤ 2 ^ 32 ∧
  (arg s 7).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 36 ≤ 2 ^ 32 ∧ roundsOk s 1

def streamFinishX86 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a c →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = c.length →
      bytesAt s'.mem ((arg s 7).setWidth 64) 16 = fullTag ciph h iv a c
  pub := pubN 8

/-- `vg_aes_gcm_stream_verify(ctx, rounds, state, aad_len, text_len, work, tag_len)`. -/
def verifyPre (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let st : Region := ⟨(arg s 2).setWidth 64, 80⟩
  let scr : Region := ⟨(arg s 7).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 36⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx] ∧ s.wr = [st, scr, args] ∧
  ctx.Disjoint st ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ st.Disjoint scr ∧ st.Disjoint args ∧
  scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint st ∧ ret.Disjoint scr ∧ ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint st ∧ stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + 80 ≤ 2 ^ 32 ∧
  (arg s 7).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 40 ≤ 2 ^ 32 ∧ roundsOk s 1

def streamVerifyX86 : Contract isa where
  pre := verifyPre
  post s s' :=
    let ciph := ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat
    let h := ctxH s.mem ((arg s 0).setWidth 64)
    ∀ iv a c, StreamRepr s.mem ((arg s 2).setWidth 64) ciph h iv a c →
      arg s 4 ++ arg s 3 = BitVec.ofNat 64 a.length → (arg s 6 ++ arg s 5).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk (arg s 8).toNat ∧ t.take (arg s 8).toNat = bytesAt s.mem ((arg s 7).setWidth 64) (arg s 8).toNat then
        (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 7).setWidth 64) 16 = t
      else (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧ bytesAt s'.mem ((arg s 7).setWidth 64) 16 = zeros 16
  pub := pubN 9

/-- `vg_aes_gcm_seal` and `_open(ctx, rounds, nonce, nonce_len, aad, aad_len, data, len, work[, tag_len])`,
with `nA` stack arguments. -/
def onePre (nA : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨(arg s 0).setWidth 64, 256⟩
  let nonce : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
  let aad : Region := ⟨(arg s 4).setWidth 64, (arg s 5).toNat⟩
  let data : Region := ⟨(arg s 6).setWidth 64, (arg s 7).toNat⟩
  let scr : Region := ⟨(arg s 8).setWidth 64, 2560⟩
  let args : Region := ⟨argAddr s 0, 4 * nA⟩
  let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
  let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 28, 28⟩
  s.rd = [ctx, nonce, aad] ∧ s.wr = [data, scr, args] ∧
  ctx.Disjoint data ∧ ctx.Disjoint scr ∧ ctx.Disjoint args ∧ nonce.Disjoint data ∧ nonce.Disjoint scr ∧
  nonce.Disjoint args ∧ aad.Disjoint data ∧ aad.Disjoint scr ∧ aad.Disjoint args ∧ data.Disjoint scr ∧
  data.Disjoint args ∧ scr.Disjoint args ∧
  ret.Disjoint ctx ∧ ret.Disjoint nonce ∧ ret.Disjoint aad ∧ ret.Disjoint data ∧ ret.Disjoint scr ∧
  ret.Disjoint args ∧
  stack.Disjoint ctx ∧ stack.Disjoint nonce ∧ stack.Disjoint aad ∧ stack.Disjoint data ∧
  stack.Disjoint scr ∧ stack.Disjoint args ∧
  (arg s 0).toNat + 256 ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
  (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + (arg s 7).toNat ≤ 2 ^ 32 ∧
  (arg s 8).toNat + 2560 ≤ 2 ^ 32 ∧ 28 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 4 + 4 * nA ≤ 2 ^ 32 ∧
  roundsOk s 1

def sealX86 : Contract isa where
  pre := onePre 9
  post s s' :=
    encryptWith (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxH s.mem ((arg s 0).setWidth 64)) 16
        (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat) (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat)
        (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat) =
      (bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat, bytesAt s'.mem ((arg s 8).setWidth 64) 16)
  pub := pubN 9

/-- What `open` computes. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem ((arg s 0).setWidth 64) (arg s 1).toNat) (ctxH s.mem ((arg s 0).setWidth 64))
    (arg s 9).toNat (bytesAt s.mem ((arg s 2).setWidth 64) (arg s 3).toNat)
    (bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat) (bytesAt s.mem ((arg s 4).setWidth 64) (arg s 5).toNat)
    (bytesAt s.mem ((arg s 8).setWidth 64) (arg s 9).toNat)

def openX86 : Contract isa where
  pre := onePre 10
  post s s' :=
    match openRes s with
    | some pt => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 1 ∧ bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = pt
    | none => (s'.gpr .edx ++ s'.gpr .eax).setWidth 32 = 0 ∧
      bytesAt s'.mem ((arg s 6).setWidth 64) (arg s 7).toNat = bytesAt s.mem ((arg s 6).setWidth 64) (arg s 7).toNat
  pub s₁ s₂ := pubN 10 s₁ s₂ ∧ (openRes s₁).isSome = (openRes s₂).isSome

/-- The `u32` a function returns, from `edx:eax`: `eax`. -/
theorem ret32_eq (a b : BitVec 32) : (a ++ b).setWidth 32 = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt b.isLt]
  omega

end VG.Proof.AesGcm.X86
