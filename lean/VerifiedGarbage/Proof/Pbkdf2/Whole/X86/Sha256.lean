import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.CT
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Hmac.Generic.X86.Hashes

/-!
# PBKDF2-HMAC-SHA-256 on x86 (32-bit), the whole derivation, for every backend

Untrusted: everything here is checked by Lean. The generic proof (`CT.lean`)
at SHA-256, for any backend (`Proof/Sha256/X86/Variants/Interface.lean`):
its streaming functions, verified for any initial hash value, give
`HashOK` at `H0`; its HMAC and PBKDF2 functions, verified against SHA-256's
own contracts with 20 bytes of stack, are moved to the shared ones with 48
(`pre_20_of_48`, and a weaker postcondition for HMAC's `finalize`). The
taint checks depend only on the sizes, so they are evaluated once, for any
backend (`sha256Shape`).
-/

namespace VG.Proof.Pbkdf2.Whole.X86

open VG.X86
open VG.Impl.Pbkdf2.Whole.X86 (Fns)
open VG.Proof.Hmac.Generic.X86 (HashOK nosp_of)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- The functions `pbkdf2` calls for SHA-256 with the backend `v`. -/
abbrev sha256FnsOf (v : Backend) : Fns := sha256Fns v.suffix v.cmpN v.cmpC v.updC v.finC

/-- SHA-256's streaming functions with the backend `v`, verified. -/
def sha256OK (v : Backend) : HashOK (sha256FnsOf v).H where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := show 32 ≤ 32 by decide
  hF := show 32 ≤ 64 by decide
  hD0 := show 0 < 32 by decide
  hS0 := show 0 < 96 by decide
  hSB := show 96 ≤ 256 by decide
  hB0 := show 0 < 64 by decide
  hBB := show 64 ≤ 128 by decide
  hWb := show 160 ≤ 8 * 20 by decide
  hW := show 20 ≤ 64 by decide
  repr := Whole.sha256_repr
  init := Proof.Sha256.X86.Stream.init_verified
  upd := v.upd.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.upd.2.2 }
  fin := v.fin.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.fin.2.2 }
  initSp := show NoSp Impl.Sha256.X86.Stream.init from nosp_of (by lit_decide)
  updSp := v.updNoSp
  finSp := v.finNoSp
  initSU := show stackUse Impl.Sha256.X86.Stream.init ≤ 20 by lit_decide
  updSU := v.updStack
  finSU := v.finStack

/-- A contract with 48 bytes of stack asks more than with 20. -/
theorem pre_20_of_48 {sig : Sig} {pre : Curry (sig.words X86.abi.ptrBits) (Mem → Prop)} {post : sig.Post X86.abi.ptrBits}
    {wa : Bool}
    {s : State} (h : (sig.contract X86.abi pre post wa 48).pre s) : (sig.contract X86.abi pre post wa 20).pre s := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · obtain ⟨wf, rd, wr, pw, res, bnd, p⟩ := h
    refine ⟨⟨by have := wf.1; omega, wf.2⟩, rd, wr, pw, fun r hr a ha => ?_, bnd, p⟩
    simp only [X86.abi, stackBelow, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact res _ (by simp [X86.abi]) a ha
    · exact (res ⟨(s.gpr .esp).setWidth 64 - BitVec.ofNat 64 48, 48⟩ (by simp [X86.abi, stackBelow]) a ha).sub_left
        (Taint.below_sub (by decide) (by decide))

/-- The functions `pbkdf2` calls for SHA-256 with the backend `v`, verified. -/
def sha256OKF (v : Backend) : FnsOK (sha256FnsOf v) where
  hH := sha256OK v
  Wi := 76
  Wf := 86
  Wt := 104
  hi := (Sound.of_verified (Proof.Hmac.Sha256.X86.Init.verified v.cmp v.cmpSp v.cmpStack v.initCt)).weaken
    (fun _ h => pre_20_of_48 h) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
  hf := (Sound.of_verified (Proof.Hmac.Sha256.X86.Finalize.verified v.cmp v.cmpSp v.cmpStack v.finHashSp
      v.finHashStack v.finCt)).weaken (fun _ h => pre_20_of_48 h) (fun s s' _ h => by
        sig_post [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.finalizeSha256OutContract,
          Spec.Hmac.finalizeSha256OutSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86.abi, X86.argSlots, X86.argVal,
          X86.argBytes] at h ⊢
        intro k0 text hl _ hr hc ho
        exact h k0 text hl hr hc ho) (fun _ _ _ _ h => h)
  it := (Sound.of_verified (Proof.Pbkdf2.Sha256.X86.verified v.cmp v.cmpSp v.cmpStack v.iterCt)).weaken
    (fun _ h => pre_20_of_48 h) (fun _ _ _ h => h) (fun _ _ _ _ h => h)
  hiSp := v.initNoSp
  hfSp := v.finalizeNoSp
  itSp := v.iterNoSp
  hiSU := v.initStack
  hfSU := v.finalizeStack
  itSU := v.iterStack
  hWi := show 76 ≤ 104 by decide
  hWf := show 86 ≤ 104 by decide
  hWt := show 104 ≤ 104 by decide
  hWH := show 20 ≤ 104 by decide
  hW := show 104 ≤ 512 by decide
  hDB := show 32 ≤ 64 by decide
  hBS := show 64 ≤ 96 by decide
  fits := show 20 + 2 * 32 + 32 ≤ 4 * 96 by decide

/-- The sizes of `sha256FnsOf`, which are all the taint checks depend on. -/
def sha256Shape : Fns := sha256Fns "" "" (.block []) (.block []) (.block [])

theorem sha256Shape_checks : Checks sha256Shape where
  pro := ⟨_, by taint_decide⟩
  cmp := ⟨_, by taint_decide⟩
  hk1 := ⟨_, by taint_decide⟩
  hk3 := ⟨_, by taint_decide⟩
  hk5 := ⟨_, by taint_decide⟩
  hk7 := ⟨_, by taint_decide⟩
  short := ⟨_, by taint_decide⟩
  su1 := ⟨_, by taint_decide⟩
  su3 := ⟨_, by taint_decide⟩
  su4 := ⟨_, by taint_decide⟩
  init := ⟨_, by taint_decide⟩
  b1 := ⟨_, by taint_decide⟩
  b2 := ⟨_, by taint_decide⟩
  b4 := ⟨_, by taint_decide⟩
  b6 := ⟨_, by taint_decide⟩
  b7 := ⟨_, by taint_decide⟩
  tail := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha256_checks (v : Backend) : Checks (sha256FnsOf v) :=
  let h := sha256Shape_checks
  ⟨h.pro, h.cmp, h.hk1, h.hk3, h.hk5, h.hk7, h.short, h.su1, h.su3, h.su4, h.init, h.b1, h.b2, h.b4, h.b6, h.b7,
    h.tail, h.restore⟩

theorem sha256_sat : ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86.abi,
    X86.argSlots, X86.argVal, X86.argBytes] [pbkSat, pbkMem] using pbkSat 200

/-- `pbkdf2` for SHA-256 with the backend `v`, verified. -/
theorem sha256_verified (v : Backend) :
    Verified X86.target (sha256FnsOf v).pbkdf2 (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76) :=
  verified (sha256OKF v) (sha256_checks v) rfl rfl sha256_sat

end VG.Proof.Pbkdf2.Whole.X86
