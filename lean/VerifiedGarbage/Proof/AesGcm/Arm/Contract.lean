import VerifiedGarbage.Proof.AesGcm.Arm.Fn
import VerifiedGarbage.Spec.Gcm.Contract

/-!
# AES-GCM on ARMv7: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. The artifacts' contracts are
the shared ones of `Spec/Gcm/Contract.lean`, which imply these
(`Verified.lean`). Every function calls others in frames that push their
stack arguments in the 8 bytes below the stack pointer (`below`), which no
buffer overlaps.
-/

namespace VG.Proof.AesGcm.Arm

open VG VG.Arm
open VG.Spec.Aes (bytesAt)
open VG.Spec.Gcm (StreamRepr KeyRepr ctxCiph ctxH gctr inc32 j0 fullTag tagLenOk zeros encryptWith openResult)

/-- The 8 bytes below the stack pointer. -/
abbrev bel (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 8⟩

/-- The `i`-th argument on the stack. -/
abbrev arg (s : State) (i : Nat) : BitVec 32 := stackArg s i

/-- The arguments on the stack, `n` words of them. -/
abbrev args (s : State) (n : Nat) : Region := ⟨stackArgAddr s 0, 4 * n⟩

abbrev roundsOk (s : State) : Prop :=
  (s.gpr .r1).toNat = 10 ∨ (s.gpr .r1).toNat = 12 ∨ (s.gpr .r1).toNat = 14

/-- A 64-bit argument on the stack, from word `i`. -/
abbrev arg64 (s : State) (i : Nat) : BitVec 64 := stackArg s (i + 1) ++ stackArg s i

/-- `vg_aes_gcm_init(key = r0, key_len = r1, ctx = r2, scratch = r3)`. -/
def initArm : Contract isa where
  pre s :=
    let key : Region := ⟨State.addr (s.gpr .r0), (s.gpr .r1).toNat⟩
    let ctx : Region := ⟨State.addr (s.gpr .r2), 256⟩
    let scr : Region := ⟨State.addr (s.gpr .r3), 2560⟩
    s.rd = [key] ∧ s.wr = [ctx, scr] ∧
      key.Disjoint ctx ∧ key.Disjoint scr ∧ ctx.Disjoint scr ∧
      (bel s).Disjoint key ∧ (bel s).Disjoint ctx ∧ (bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 256 ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      ((s.gpr .r1).toNat = 16 ∨ (s.gpr .r1).toNat = 24 ∨ (s.gpr .r1).toNat = 32)
  post s s' := KeyRepr s'.mem (State.addr (s.gpr .r2)) (bytesAt s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat)
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3

/-- `vg_aes_gcm_stream_init(ctx = r0, nonce = r1, nonce_len = r2, state = r3, scratch = [sp])`. -/
def streamInitArm : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let nonce : Region := ⟨State.addr (s.gpr .r1), (s.gpr .r2).toNat⟩
    let st : Region := ⟨State.addr (s.gpr .r3), 80⟩
    let scr : Region := ⟨State.addr (arg s 0), 2560⟩
    s.rd = [ctx, nonce, args s 1] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ nonce.Disjoint st ∧ nonce.Disjoint scr ∧ st.Disjoint scr ∧
      st.Disjoint (args s 1) ∧ scr.Disjoint (args s 1) ∧
      (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint st ∧ (bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 0).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' := ∀ ciph, StreamRepr s'.mem (State.addr (s.gpr .r3)) ciph (ctxH s.mem (State.addr (s.gpr .r0)))
    (bytesAt s.mem (State.addr (s.gpr .r1)) (s.gpr .r2).toNat) [] []
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ arg s₁ 0 = arg s₂ 0

/-- `vg_aes_gcm_stream_aad(ctx = r0, state = r1, aad_len = r3:r2, data = [sp], len = [sp + 4],
scratch = [sp + 8])`. -/
def streamAadArm : Contract isa where
  pre s :=
    let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
    let st : Region := ⟨State.addr (s.gpr .r1), 80⟩
    let data : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
    let scr : Region := ⟨State.addr (arg s 2), 2560⟩
    s.rd = [ctx, data, args s 3] ∧ s.wr = [st, scr] ∧
      ctx.Disjoint st ∧ ctx.Disjoint scr ∧ data.Disjoint st ∧ data.Disjoint scr ∧ st.Disjoint scr ∧
      st.Disjoint (args s 3) ∧ scr.Disjoint (args s 3) ∧
      (bel s).Disjoint ctx ∧ (bel s).Disjoint data ∧ (bel s).Disjoint st ∧ (bel s).Disjoint scr ∧
      (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 80 ≤ 2 ^ 32 ∧
      (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
      s.sp.toNat + 12 ≤ 2 ^ 32
  post s s' := ∀ ciph iv a, StreamRepr s.mem (State.addr (s.gpr .r1)) ciph (ctxH s.mem (State.addr (s.gpr .r0))) iv a [] →
    (s.gpr .r3 ++ s.gpr .r2) = BitVec.ofNat 64 a.length →
    StreamRepr s'.mem (State.addr (s.gpr .r1)) ciph (ctxH s.mem (State.addr (s.gpr .r0))) iv
      (a ++ bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat) []
  pub s₁ s₂ := s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2

/-- What `vg_aes_gcm_stream_encrypt` and `vg_aes_gcm_stream_decrypt` need:
`(ctx = r0, rounds = r1, state = r2, aad_len = [sp + 4]:[sp], text_len = [sp + 12]:[sp + 8],
data = [sp + 16], len = [sp + 20], scratch = [sp + 24])`. -/
def streamCryptPre (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r2), 80⟩
  let data : Region := ⟨State.addr (arg s 4), (arg s 5).toNat⟩
  let scr : Region := ⟨State.addr (arg s 6), 2560⟩
  s.rd = [ctx, args s 7] ∧ s.wr = [st, data, scr] ∧
    ctx.Disjoint st ∧ ctx.Disjoint data ∧ ctx.Disjoint scr ∧
    st.Disjoint data ∧ st.Disjoint scr ∧ st.Disjoint (args s 7) ∧ data.Disjoint scr ∧
    data.Disjoint (args s 7) ∧ scr.Disjoint (args s 7) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint st ∧ (bel s).Disjoint data ∧ (bel s).Disjoint scr ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 80 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + (arg s 5).toNat ≤ 2 ^ 32 ∧ (arg s 6).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧
    s.sp.toNat + 28 ≤ 2 ^ 32 ∧ roundsOk s

def streamCryptPub (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    ∀ i < 7, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_stream_encrypt`. -/
def streamEncryptArm : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a p, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a (gctr ciph (inc32 (j0 h iv)) p) →
      arg64 s 0 = BitVec.ofNat 64 a.length → (arg64 s 2).toNat = p.length →
      let c := gctr ciph (inc32 (j0 h iv)) (p ++ bytesAt s.mem (State.addr (arg s 4)) (arg s 5).toNat)
      StreamRepr s'.mem (State.addr (s.gpr .r2)) ciph h iv a c ∧
        bytesAt s'.mem (State.addr (arg s 4)) (arg s 5).toNat = c.drop p.length
  pub := streamCryptPub

/-- `vg_aes_gcm_stream_decrypt`. -/
def streamDecryptArm : Contract isa where
  pre := streamCryptPre
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a c →
      arg64 s 0 = BitVec.ofNat 64 a.length → (arg64 s 2).toNat = c.length →
      let c' := c ++ bytesAt s.mem (State.addr (arg s 4)) (arg s 5).toNat
      StreamRepr s'.mem (State.addr (s.gpr .r2)) ciph h iv a c' ∧
        bytesAt s'.mem (State.addr (arg s 4)) (arg s 5).toNat = (gctr ciph (inc32 (j0 h iv)) c').drop c.length
  pub := streamCryptPub

/-- What `vg_aes_gcm_stream_finish` needs: `(ctx = r0, rounds = r1, state = r2,
aad_len = [sp + 4]:[sp], text_len = [sp + 12]:[sp + 8], work = [sp + 16])`, and
`vg_aes_gcm_stream_verify` with `tag_len = [sp + 20]` (`n` words of stack
arguments). -/
def finPre (n : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let st : Region := ⟨State.addr (s.gpr .r2), 80⟩
  let work : Region := ⟨State.addr (arg s 4), 2560⟩
  s.rd = [ctx, args s n] ∧ s.wr = [st, work] ∧
    ctx.Disjoint st ∧ ctx.Disjoint work ∧ st.Disjoint work ∧ st.Disjoint (args s n) ∧
    work.Disjoint (args s n) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint st ∧ (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 4).toNat + 2560 ≤ 2 ^ 32 ∧
    8 ≤ s.sp.toNat ∧ s.sp.toNat + 4 * n ≤ 2 ^ 32 ∧ roundsOk s

def finPub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    ∀ i < n, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_stream_finish`. -/
def streamFinishArm : Contract isa where
  pre := finPre 5
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a c →
      arg64 s 0 = BitVec.ofNat 64 a.length → (arg64 s 2).toNat = c.length →
      bytesAt s'.mem (State.addr (arg s 4)) 16 = fullTag ciph h iv a c
  pub := finPub 5

/-- `vg_aes_gcm_stream_verify`. -/
def streamVerifyArm : Contract isa where
  pre := finPre 6
  post s s' :=
    let ciph := ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat
    let h := ctxH s.mem (State.addr (s.gpr .r0))
    let tl := (arg s 5).toNat
    ∀ iv a c, StreamRepr s.mem (State.addr (s.gpr .r2)) ciph h iv a c →
      arg64 s 0 = BitVec.ofNat 64 a.length → (arg64 s 2).toNat = c.length →
      let t := fullTag ciph h iv a c
      if tagLenOk tl ∧ t.take tl = bytesAt s.mem (State.addr (arg s 4)) tl then
        s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s 4)) 16 = t
      else s'.gpr .r0 = 0 ∧ bytesAt s'.mem (State.addr (arg s 4)) 16 = zeros 16
  pub := finPub 6

/-- What `vg_aes_gcm_seal` needs: `(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3, aad = [sp],
aad_len = [sp + 4], data = [sp + 8], len = [sp + 12], work = [sp + 16])`, and `vg_aes_gcm_open`
with `tag_len = [sp + 20]` (`n` words of stack arguments). -/
def onePre (n : Nat) (s : State) : Prop :=
  let ctx : Region := ⟨State.addr (s.gpr .r0), 256⟩
  let nonce : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
  let aad : Region := ⟨State.addr (arg s 0), (arg s 1).toNat⟩
  let data : Region := ⟨State.addr (arg s 2), (arg s 3).toNat⟩
  let work : Region := ⟨State.addr (arg s 4), 2560⟩
  s.rd = [ctx, nonce, aad, args s n] ∧ s.wr = [data, work] ∧
    ctx.Disjoint data ∧ ctx.Disjoint work ∧ nonce.Disjoint data ∧ nonce.Disjoint work ∧
    aad.Disjoint data ∧ aad.Disjoint work ∧
    data.Disjoint work ∧ data.Disjoint (args s n) ∧ work.Disjoint (args s n) ∧
    (bel s).Disjoint ctx ∧ (bel s).Disjoint nonce ∧ (bel s).Disjoint aad ∧ (bel s).Disjoint data ∧
    (bel s).Disjoint work ∧
    (s.gpr .r0).toNat + 256 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧
    (arg s 0).toNat + (arg s 1).toNat ≤ 2 ^ 32 ∧ (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 2560 ≤ 2 ^ 32 ∧ 8 ≤ s.sp.toNat ∧ s.sp.toNat + 4 * n ≤ 2 ^ 32 ∧ roundsOk s

def onePub (n : Nat) (s₁ s₂ : State) : Prop :=
  s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.gpr .r2 = s₂.gpr .r2 ∧
    s₁.gpr .r3 = s₂.gpr .r3 ∧ ∀ i < n, arg s₁ i = arg s₂ i

/-- `vg_aes_gcm_seal`. -/
def sealArm : Contract isa where
  pre := onePre 5
  post s s' :=
    encryptWith (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0))) 16
        (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat) (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat)
        (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat) =
      (bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat, bytesAt s'.mem (State.addr (arg s 4)) 16)
  pub := onePub 5

/-- What `vg_aes_gcm_open` computes, in a state. -/
abbrev openRes (s : State) : Option (List Byte) :=
  openResult (ctxCiph s.mem (State.addr (s.gpr .r0)) (s.gpr .r1).toNat) (ctxH s.mem (State.addr (s.gpr .r0)))
    (arg s 5).toNat (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    (bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat) (bytesAt s.mem (State.addr (arg s 0)) (arg s 1).toNat)
    (bytesAt s.mem (State.addr (arg s 4)) (arg s 5).toNat)

/-- `vg_aes_gcm_open`. -/
def openArm : Contract isa where
  pre := onePre 6
  post s s' :=
    match openRes s with
    | some pt => s'.gpr .r0 = 1 ∧ bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = pt
    | none => s'.gpr .r0 = 0 ∧
        bytesAt s'.mem (State.addr (arg s 2)) (arg s 3).toNat = bytesAt s.mem (State.addr (arg s 2)) (arg s 3).toNat
  pub s₁ s₂ := onePub 6 s₁ s₂ ∧ (openRes s₁).isSome = (openRes s₂).isSome

end VG.Proof.AesGcm.Arm
