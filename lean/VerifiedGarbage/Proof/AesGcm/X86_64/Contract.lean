import VerifiedGarbage.Proof.AesGcm.X86_64.Fn
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). Every function calls others, whose return addresses are
in the 8 bytes below the stack pointer (`stk`), which no buffer overlaps,
nor the return address (`ret`).
-/

namespace VG.Proof.AesGcm

open VG VG.X86_64
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- The return address. -/
abbrev ret (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- The stack the calls use. -/
abbrev stk (s : State) : Region := below (s.gpr .rsp) 8

/-- The stack `seal` and `open` use: a frame of one argument, and the return
addresses of a call and of its own calls. -/
abbrev stk24 (s : State) : Region := below (s.gpr .rsp) 24

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 64 := stackArg s i

/-- The arguments on the stack, `n` of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 8 * n⟩

abbrev rounds (s : State) : Prop :=
  (s.gpr .rsi).toNat = 10 ∨ (s.gpr .rsi).toNat = 12 ∨ (s.gpr .rsi).toNat = 14

/-- `vg_aes_gcm_init(key = rdi, key_len = rsi, ctx = rdx, scratch = rcx)`. -/
def initX86_64 : Contract isa where
  pre s :=
    let key : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let ctx : Region := ⟨s.gpr .rdx, 256⟩
    let scr : Region := ⟨s.gpr .rcx, 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧ (ret s).Disjoint ctx ∧ (ret s).Disjoint scr ∧
      (stk s).Disjoint key ∧ (stk s).Disjoint ctx ∧ (stk s).Disjoint scr ∧
      (s.gpr .rdx).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + 2560 ≤ 2 ^ 64 ∧
      ((s.gpr .rsi).toNat = 16 ∨ (s.gpr .rsi).toNat = 24 ∨ (s.gpr .rsi).toNat = 32)
  post s s' := KeyRepr s'.mem (s.gpr .rdx) (bytesAt s.mem (s.gpr .rdi) (s.gpr .rsi).toNat)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_gcm_stream_init(ctx = rdi, nonce = rsi, nonce_len = rdx, state = rcx, scratch = r8)`. -/
def streamInitX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 256⟩
    let nonce : Region := ⟨s.gpr .rsi, (s.gpr .rdx).toNat⟩
    let st : Region := ⟨s.gpr .rcx, 80⟩
    let scr : Region := ⟨s.gpr .r8, 2560⟩
    s.rd = [ctx, nonce] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      (ret s).Disjoint st ∧ (ret s).Disjoint scr ∧
      (stk s).Disjoint ctx ∧ (stk s).Disjoint nonce ∧ (stk s).Disjoint st ∧ (stk s).Disjoint scr ∧
      (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + (s.gpr .rdx).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rcx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r8).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph, StreamRepr s'.mem (s.gpr .rcx) ciph (ctxH s.mem (s.gpr .rdi))
    (bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat) [] []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_gcm_stream_aad(ctx = rdi, state = rsi, aad_len = rdx, data = rcx, len = r8, scratch = r9)`. -/
def streamAadX86_64 : Contract isa where
  pre s :=
    let ctx : Region := ⟨s.gpr .rdi, 256⟩
    let st : Region := ⟨s.gpr .rsi, 80⟩
    let data : Region := ⟨s.gpr .rcx, (s.gpr .r8).toNat⟩
    let scr : Region := ⟨s.gpr .r9, 2560⟩
    s.rd = [ctx, data] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      (ret s).Disjoint st ∧ (ret s).Disjoint scr ∧
      (stk s).Disjoint ctx ∧ (stk s).Disjoint data ∧ (stk s).Disjoint st ∧ (stk s).Disjoint scr ∧
      (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + (s.gpr .r8).toNat ≤ 2 ^ 64 ∧
      (s.gpr .rsi).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64
  post s s' := ∀ ciph iv a, StreamRepr s.mem (s.gpr .rsi) ciph (ctxH s.mem (s.gpr .rdi)) iv a [] →
    s.gpr .rdx = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (s.gpr .rsi) ciph (ctxH s.mem (s.gpr .rdi)) iv
      (a ++ bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat) []
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx, text_len = r8, data = r9, len = [rsp + 8],
scratch = [rsp + 16])`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let data : Region := ⟨s.gpr .r9, (arg s 0).toNat⟩
  let scr : Region := ⟨arg s 1, 2560⟩
  s.rd = [ctx, args s 2] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ st.Disjoint (args s 2) ∧ data.Disjoint scr ∧
    data.Disjoint (args s 2) ∧ scr.Disjoint (args s 2) ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint data ∧ (ret s).Disjoint scr ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint data ∧ (stk s).Disjoint scr ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧
    (s.gpr .r9).toNat + (arg s 0).toNat ≤ 2 ^ 64 ∧ (arg s 1).toNat + 2560 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 24 ≤ 2 ^ 64 ∧ rounds s

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptX86_64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a p, StreamRepr s.mem (s.gpr .rdx) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (s.gpr .r9) (arg s 0).toNat)
      StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c ∧ bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptX86_64 : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      let c' := c ++ bytesAt s.mem (s.gpr .r9) (arg s 0).toNat
      StreamRepr s'.mem (s.gpr .rdx) ciph h iv a c' ∧
        bytesAt s'.mem (s.gpr .r9) (arg s 0).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = rdi, rounds = rsi, state = rdx, aad_len = rcx,
text_len = r8, work = r9)`. -/
def finPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let work : Region := ⟨s.gpr .r9, 2560⟩
  s.rd = [ctx] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint work ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64 ∧
    rounds s

/-- What `vg_aes_gcm_stream_verify` needs: those and `tag_len = [rsp + 8]`. -/
def verifyPre (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let st : Region := ⟨s.gpr .rdx, 80⟩
  let work : Region := ⟨s.gpr .r9, 2560⟩
  s.rd = [ctx, args s 1] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ st.Disjoint (args s 1) ∧
    work.Disjoint (args s 1) ∧
    (ret s).Disjoint st ∧ (ret s).Disjoint work ∧
    (stk s).Disjoint ctx ∧ (stk s).Disjoint st ∧ (stk s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + 80 ≤ 2 ^ 64 ∧ (s.gpr .r9).toNat + 2560 ≤ 2 ^ 64 ∧
    (s.gpr .rsp).toNat + 16 ≤ 2 ^ 64 ∧ rounds s

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishX86_64 : Contract isa where
  pre := finPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      bytesAt s'.mem (s.gpr .r9) 16 = fullTag ciph h iv a c
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyX86_64 : Contract isa where
  pre := verifyPre
  post s s' :=
    let ciph := ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat
    let h := ctxH s.mem (s.gpr .rdi)
    let tl := (arg s 0).toNat
    ∀ iv a c, StreamRepr s.mem (s.gpr .rdx) ciph h iv a c →
      s.gpr .rcx = BitVec.ofNat 64 a.length → (s.gpr .r8).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (s.gpr .r9) tl then
        (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (s.gpr .r9) 16 = t
      else (s'.gpr .rax).setWidth 32 = 0 ∧ bytesAt s'.mem (s.gpr .r9) 16 = zeros 16
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    arg s₁ 0 = arg s₂ 0

/-- What `vg_aes_gcm_seal` needs: `(ctx = rdi, rounds = rsi, nonce = rdx, nonce_len = rcx, aad = r8,
aad_len = r9, data = [rsp + 8], len = [rsp + 16], work = [rsp + 24])`, and `vg_aes_gcm_open` with
`tag_len = [rsp + 32]`. -/
def onePre (n : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨s.gpr .rdi, 256⟩
  let nonce : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
  let aad : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
  let data : Region := ⟨arg s 0, (arg s 1).toNat⟩
  let work : Region := ⟨arg s 2, 2560⟩
  s.rd = [ctx, nonce, aad, args s n] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (ret s).Disjoint data ∧ (ret s).Disjoint work ∧
    (stk24 s).Disjoint ctx ∧ (stk24 s).Disjoint nonce ∧ (stk24 s).Disjoint aad ∧ (stk24 s).Disjoint data ∧
    (stk24 s).Disjoint work ∧
    (s.gpr .rdi).toNat + 256 ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat ≤ 2 ^ 64 ∧
    (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 64 ∧
    (arg s 2).toNat + 2560 ≤ 2 ^ 64 ∧ 24 ≤ (s.gpr .rsp).toNat ∧ (s.gpr .rsp).toNat + 8 * (n + 1) ≤ 2 ^ 64 ∧
    rounds s

def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .r9 = s₂.gpr .r9 ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealX86_64 : Contract isa where
  pre := onePre 3
  post s s' :=
    encryptWith (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) 16
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) =
      (bytesAt s'.mem (arg s 0) (arg s 1).toNat, bytesAt s'.mem (arg s 2) 16)
  pub := onePub 3

/-- `vg_aes_gcm_open`. -/
def openX86_64 : Contract isa where
  pre := onePre 4
  post s s' :=
    match openResult (ctxCiph s.mem (s.gpr .rdi) (s.gpr .rsi).toNat) (ctxH s.mem (s.gpr .rdi)) (arg s 3).toNat
        (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) (bytesAt s.mem (arg s 0) (arg s 1).toNat)
        (bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) (bytesAt s.mem (arg s 2) (arg s 3).toNat) with
    | some pt => (s'.gpr .rax).setWidth 32 = 1 ∧ bytesAt s'.mem (arg s 0) (arg s 1).toNat = pt
    | none => (s'.gpr .rax).setWidth 32 = 0 ∧
        bytesAt s'.mem (arg s 0) (arg s 1).toNat = bytesAt s.mem (arg s 0) (arg s 1).toNat
  pub s₁ s₂ := onePub 4 s₁ s₂ ∧
    (openResult (ctxCiph s₁.mem (s₁.gpr .rdi) (s₁.gpr .rsi).toNat) (ctxH s₁.mem (s₁.gpr .rdi)) (arg s₁ 3).toNat
        (bytesAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat) (bytesAt s₁.mem (arg s₁ 0) (arg s₁ 1).toNat)
        (bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat) (bytesAt s₁.mem (arg s₁ 2) (arg s₁ 3).toNat)).isSome =
      (openResult (ctxCiph s₂.mem (s₂.gpr .rdi) (s₂.gpr .rsi).toNat) (ctxH s₂.mem (s₂.gpr .rdi)) (arg s₂ 3).toNat
        (bytesAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat) (bytesAt s₂.mem (arg s₂ 0) (arg s₂ 1).toNat)
        (bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat) (bytesAt s₂.mem (arg s₂ 2) (arg s₂ 3).toNat)).isSome

end VG.Proof.AesGcm
