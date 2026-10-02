import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Instances
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
import VerifiedGarbage.Proof.Hmac.Arm.Init
import VerifiedGarbage.Proof.Hmac.Arm.Finalize
import VerifiedGarbage.Proof.Pbkdf2.Arm.Iterate
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# PBKDF2-HMAC-SHA-256 on 32-bit ARM, the whole derivation

The generic proof (`CT.lean`) at SHA-256: its streaming functions, verified
for any initial hash value, give `HashOK` at `H0`; its HMAC and PBKDF2
functions, verified against SHA-256's own contracts with no stack, are moved
to the shared ones with 16 bytes of stack (`pre_0_of_16`, and a weaker
postcondition for HMAC's `finalize`).
-/

namespace VG.Proof.Pbkdf2.Whole.Arm

open VG.Arm
open VG.Impl.Pbkdf2.Whole.Arm (Fns)
open VG.Proof.Hmac.Generic.Arm (HashOK)

/-- SHA-256's streaming functions. -/
def sha256H : Impl.Hmac.Generic.Arm.Hash := ⟨64, 96, 32, 32, 20, Spec.Sha256.initApi.name,
  Impl.Sha256.Arm.Stream.init, Spec.Sha256.updateApi.name, Impl.Sha256.Arm.Stream.update,
  Spec.Sha256.finalizeApi.name, Impl.Sha256.Arm.Stream.finalize⟩

/-- SHA-256's streaming functions, verified. -/
def sha256OK : HashOK sha256H where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by decide
  hF := by decide
  hD0 := by decide
  hS0 := by decide
  hSB := by decide
  hB0 := by decide
  hBB := by decide
  hWb := by decide
  hW := by decide
  repr := Whole.sha256_repr
  init := Proof.Sha256.Arm.Stream.init_verified
  upd := Proof.Sha256.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

/-- A contract with 16 bytes of stack asks more than with none. -/
theorem pre_0_of_16 {sig : Sig} {pre : Curry (sig.words Arm.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post Arm.abi.ptrBits} {wa : Bool} {s : State}
    (h : (sig.contract Arm.abi pre post wa 16).pre s) : (sig.contract Arm.abi pre post wa 0).pre s := by
  simp only [Sig.contract] at h ⊢
  split at h
  · exact h.elim
  · obtain ⟨wf, rd, wr, pw, _, bnd, p⟩ := h
    exact ⟨wf.2, rd, wr, pw, fun r hr => by simp [Arm.abi, stackBelow] at hr, bnd, p⟩

/-- The functions `pbkdf2` calls for SHA-256. -/
def sha256F : Fns where
  H := sha256H
  W := Spec.Hmac.sha256I.scratch
  hiN := Spec.Hmac.initSha256Api.name
  hiC := Impl.Hmac.Arm.init
  hfN := Spec.Hmac.finalizeSha256OutApi.name
  hfC := Impl.Hmac.Arm.finalize
  itN := Spec.Pbkdf2.iterateSha256Api.name
  itC := Impl.Pbkdf2.Arm.iterate

/-- The functions `pbkdf2` calls for SHA-256, verified. -/
def sha256OKF : FnsOK sha256F where
  hH := sha256OK
  Wi := 76
  Wf := 86
  Wt := 104
  hi := (Sound.of_verified Proof.Hmac.Arm.Init.init_verified).weaken (fun _ h => pre_0_of_16 h)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
  hf := (Sound.of_verified Proof.Hmac.Arm.Finalize.finalize_verified).weaken (fun _ h => pre_0_of_16 h)
    (fun s s' _ h => by
      sig_post [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.finalizeSha256OutContract,
        Spec.Hmac.finalizeSha256OutSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, Arm.abi, Arm.argRegs,
        Arm.reduceClassify, Arm.Loc.val] at h ⊢
      intro k0 text hl _ hr hc ho
      exact h k0 text hl hr hc ho) (fun _ _ _ _ h => h)
  it := (Sound.of_verified Proof.Pbkdf2.Arm.iterate_verified).weaken (fun _ h => pre_0_of_16 h)
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
  hiSt := by decide +kernel
  hfSt := by decide +kernel
  itSt := by decide +kernel
  hWi := by decide
  hWf := by decide
  hWt := by decide
  hWH := by decide
  hDB := by decide
  hBS := by decide
  fits := by decide
  reach := by decide
  encB1 := by decide
  encB := by decide
  encB4 := by decide
  encD := by decide

theorem sha256_checks : Checks sha256F := by
  constructor <;> exact ⟨_, by taint_decide⟩

theorem sha256_sat : ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24).pre s := by
  sig_implies_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig,
    Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I, Spec.Hmac.sha256S, Spec.Hmac.sha256, Arm.abi,
    Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [pbkSat, pbkMem] using pbkSat 200

/-- `pbkdf2` for SHA-256, verified. -/
theorem sha256 : Verified Arm.target sha256F.pbkdf2 (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24) :=
  verified sha256OKF sha256_checks rfl rfl sha256_sat

end VG.Proof.Pbkdf2.Whole.Arm
