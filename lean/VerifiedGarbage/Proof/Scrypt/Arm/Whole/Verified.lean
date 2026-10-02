import VerifiedGarbage.Proof.Scrypt.Arm.Whole.CT
import VerifiedGarbage.Proof.Pbkdf2.Whole.Arm.Sha256
import VerifiedGarbage.Proof.Framework.Contract

/-!
# scrypt on 32-bit ARM: the shared contract

Untrusted: everything here is checked by Lean. `vg_scrypt`, calling any
implementation of PBKDF2-HMAC-SHA256 verified against its shared contract
whose frames use at most 24 bytes of stack, is verified against
`Spec.Scrypt.scryptContract` for the 40 bytes of stack its calls use
(`scrypt_verified_of`); and so is the one calling `vg_pbkdf2_hmac_sha256`
(`scrypt_verified`).
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Arm.FrameStack

theorem map_range9 {α : Type} (f : Nat → α) :
    List.map f (List.range 9) = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8] := rfl

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
words at `0x9000`. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r2 => 0x2000
    | _ => 0
  sp := 0x9000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x9000 then 1 else if a = 0x9005 then 0x30 else if a = 0x9008 then 1
    else if a = 0x900D then 0x40 else if a = 0x9010 then 2 else if a = 0x9015 then 0x50
    else if a = 0x9018 then 17 else if a = 0x901D then 0x60 else if a = 0x9020 then 1 else 0
  rd := [⟨0x1000, 0⟩, ⟨0x2000, 0⟩, ⟨0x9000, 36⟩]
  wr := [⟨0x3000, 128⟩, ⟨0x4000, 256⟩, ⟨0x5000, 2176⟩, ⟨0x6000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptArm.Implies (Spec.Scrypt.scryptContract Arm.abi 40) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptArm, Arm.abi,
          Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, map_range9, List.append_eq] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 a0 a1 a2 a3 a4 a5 a6 a7
        exact ⟨h0, h1, h2, h3, a0, a1, a2, a3, a4, a5, a6, a7, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Arm.abi, Arm.argRegs,
          Arm.reduceClassify, Arm.Loc.val, Arm.State.addr, map_range9, List.append_eq, satState] [satState]
          using satState }

section
variable {pbk : Prog isa} (hv : Verified Arm.target pbk (Spec.Hmac.sha256I.pbkdf2Contract Arm.abi 24))
  (hst : armStack pbk ≤ 24) (name : String)
include hv hst

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified Arm.target (scrypt name pbk) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := scrypt_ok hv hst name h
    exact ⟨t, s', he, hp⟩) (scrypt_ct hv hst name) scrypt_implies

end

/-! ## With `vg_pbkdf2_hmac_sha256` -/

theorem armStack_zero {c : Prog isa} (h : c.noFrames = true) : armStack c = 0 := by
  induction c <;> simp_all [Code.noFrames, armStack]

/-- How much stack the frames of `pbkdf2` use. -/
theorem pbkdf2_stack {F : Impl.Pbkdf2.Whole.Arm.Fns} (hi : F.H.initC.noFrames = true)
    (hu : F.H.updC.noFrames = true) (hf : F.H.finC.noFrames = true) (h₁ : armStack F.hiC ≤ 16)
    (h₂ : armStack F.hfC ≤ 16) (h₃ : armStack F.itC ≤ 16) : armStack F.pbkdf2 ≤ 24 := by
  simp only [Impl.Pbkdf2.Whole.Arm.Fns.pbkdf2, Impl.Pbkdf2.Whole.Arm.Fns.key,
    Impl.Pbkdf2.Whole.Arm.Fns.hashKey, Impl.Pbkdf2.Whole.Arm.Fns.setup, Impl.Pbkdf2.Whole.Arm.Fns.block,
    Impl.Pbkdf2.Whole.Arm.Fns.outLen, Impl.Pbkdf2.Whole.Arm.Fns.outLoop, Impl.Hmac.Generic.Arm.copy,
    Impl.Hmac.Generic.Arm.Hash.callInit, armStack, armStack_zero hi, armStack_zero hu, armStack_zero hf,
    List.length_cons, List.length_nil]
  omega

/-- The code of `vg_pbkdf2_hmac_sha256`. -/
abbrev pbkC : Prog isa := Proof.Pbkdf2.Whole.Arm.sha256F.pbkdf2

theorem pbk_stack : armStack pbkC ≤ 24 :=
  pbkdf2_stack Proof.Pbkdf2.Whole.Arm.sha256OK.initNF Proof.Pbkdf2.Whole.Arm.sha256OK.updNF
    Proof.Pbkdf2.Whole.Arm.sha256OK.finNF Proof.Pbkdf2.Whole.Arm.sha256OKF.hiSt
    Proof.Pbkdf2.Whole.Arm.sha256OKF.hfSt Proof.Pbkdf2.Whole.Arm.sha256OKF.itSt

/-- `vg_scrypt`. -/
theorem scrypt_verified :
    Verified Arm.target (scrypt Spec.Hmac.sha256I.pbkdf2Api.name pbkC) (Spec.Scrypt.scryptContract Arm.abi 40) :=
  scrypt_verified_of Proof.Pbkdf2.Whole.Arm.sha256 pbk_stack _

end VG.Proof.Scrypt.Arm.Whole
