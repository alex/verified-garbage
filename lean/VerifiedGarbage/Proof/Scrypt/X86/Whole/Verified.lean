import VerifiedGarbage.Proof.Scrypt.X86.Whole.CT
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Framework.Contract

/-!
# scrypt on x86 (32-bit): the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract that never writes `esp` and uses at most 76 bytes of
stack, is verified against `Spec.Scrypt.scryptContract` for the 116 bytes of
stack its frame and calls use (`scrypt_verified_of`); and so is the one
calling the `vg_pbkdf2_hmac_sha256` made with any SHA-256 backend
(`scrypt_verified`), whose code never writes `esp` but by the frame
(`scrypt_spSafe`).
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Proof.Pbkdf2.Whole.X86 (argVal32 setWidth32_64 toNat_setWidth64 setWidth_inj32 sha256FnsOf)
open VG.Proof.Sha256.X86.Variants (Backend)

/-- Memory holding the arguments `0x1000, 0, 0x1100, 0, 1, 0x3000, 1, 0x4000, 2, 0x5000, 17, 0x6000, 1`
at `0x8004`. -/
def satMem : Mem := fun a =>
  if a = 0x8005 then 0x10 else if a = 0x800D then 0x11 else if a = 0x8014 then 1 else
  if a = 0x8019 then 0x30 else if a = 0x801C then 1 else if a = 0x8021 then 0x40 else
  if a = 0x8024 then 2 else if a = 0x8029 then 0x50 else if a = 0x802C then 17 else
  if a = 0x8031 then 0x60 else if a = 0x8034 then 1 else 0

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt. -/
def satState : State where
  gpr r := match r with
    | .esp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩]
  wr := [⟨0x3000, 128⟩, ⟨0x4000, 256⟩, ⟨0x5000, 2176⟩, ⟨0x6000, 1⟩, ⟨0x8004, 52⟩]

theorem scrypt_implies : Proof.Scrypt.scryptX86.Implies (Spec.Scrypt.scryptContract X86.abi 116) := by
  exact
    { pre := by
        intro s h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi] at h
        simp only [argVal32, setWidth32_64, toNat_setWidth64,
          show argBytes [32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32] = 52 from rfl] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi]
        simp only [argVal32, setWidth32_64]
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86, X86.abi] at h
        simp only [argVal32] at h
        obtain ⟨e, hlk, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
        refine ⟨e, fun i hi => ?_, ?_⟩
        · match i, hi with
          | 0, _ => exact setWidth_inj32 a0
          | 1, _ => exact setWidth_inj32 a1
          | 2, _ => exact setWidth_inj32 a2
          | 3, _ => exact setWidth_inj32 a3
          | 4, _ => exact setWidth_inj32 a4
          | 5, _ => exact setWidth_inj32 a5
          | 6, _ => exact setWidth_inj32 a6
          | 7, _ => exact setWidth_inj32 a7
          | 8, _ => exact setWidth_inj32 a8
          | 9, _ => exact setWidth_inj32 a9
          | 10, _ => exact setWidth_inj32 a10
          | 11, _ => exact setWidth_inj32 a11
          | 12, _ => exact setWidth_inj32 a12
        · simpa only [setWidth32_64, List.flatMap_def] using hlk
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, X86.abi, X86.argSlots,
          X86.argVal, X86.argBytes] [satState, satMem] using satState }

section
variable {pbk : Prog isa} (hv : Verified X86.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86.abi 76))
  (hsp : NoSp pbk) (hst : stackUse pbk ≤ 76) (name : String)
include hv hsp hst

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified X86.target (scrypt name pbk) (Spec.Scrypt.scryptContract X86.abi 116) :=
  Verified.of_correct (fun _ h => scrypt_ok hv hsp hst name h) (scrypt_ct hv hsp hst name) scrypt_implies

end

/-! ## With the PBKDF2 made with a SHA-256 backend -/

theorem clobbers_esp (i : Instr) : Taint.clobbers i .esp = isa.writesSp i := by
  cases i <;> rfl

theorem all_eq (p : Instr → Bool) (c : Prog isa) : c.all p = (VG.instrs c).all p := by
  induction c <;> simp_all [Code.all, VG.instrs, List.all_append, Bool.and_assoc]

/-- Code whose instructions never write `esp`, but by its frames, keeps it. -/
theorem nosp_of_all {c : Prog isa} (h : c.all (fun i => !isa.writesSp i) = true) : NoSp c := by
  intro i hi
  rw [all_eq, List.all_eq_true] at h
  rw [clobbers_esp]
  simpa using h i hi

variable (v : Backend)

/-- PBKDF2-HMAC-SHA256 made with `v`. -/
abbrev pbkOf : Prog isa := (sha256FnsOf v).pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2Api.name ++ v.suffix

theorem pbk_stack : stackUse (pbkOf v) ≤ 76 := by
  have := v.updStack; have := v.finStack; have := v.initStack; have := v.finalizeStack; have := v.iterStack
  have hi : stackUse Impl.Sha256.X86.Stream.init ≤ 20 := by lit_decide
  simp only [pbkOf, Impl.Pbkdf2.Whole.X86.Fns.pbkdf2, Impl.Pbkdf2.Whole.X86.Fns.key,
    Impl.Pbkdf2.Whole.X86.Fns.hashKey, Impl.Pbkdf2.Whole.X86.Fns.setup, Impl.Pbkdf2.Whole.X86.Fns.block,
    Impl.Pbkdf2.Whole.X86.Fns.outLen, Impl.Pbkdf2.Whole.X86.Fns.outLoop, Impl.Hmac.Generic.X86.copy,
    Impl.Hmac.Generic.X86.Hash.callInit, Proof.Pbkdf2.Whole.X86.sha256Fns, Proof.Pbkdf2.Whole.X86.sha256H,
    stackUse, frameBytes, List.length_cons, List.length_nil] at *
  omega

/-- `vg_scrypt` made with `v`. -/
theorem scrypt_verified :
    Verified X86.target (scrypt (pbkName v) (pbkOf v)) (Spec.Scrypt.scryptContract X86.abi 116) :=
  scrypt_verified_of (Proof.Pbkdf2.Whole.X86.sha256_verified v) (nosp_of_all v.pbkdf2Sp) (pbk_stack v) _

/-- No instruction writes `esp` but the frame's push and pop. -/
theorem scrypt_spSafe : (scrypt (pbkName v) (pbkOf v)).all (fun i => !isa.writesSp i) = true := by
  have hr : Impl.Scrypt.X86.roMix.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  simp only [pbkOf, scrypt, scryptBody, pbkCall, romixLoop, Code.all, v.pbkdf2Sp, hr, Bool.and_true,
    Bool.true_and]
  decide

end VG.Proof.Scrypt.X86.Whole
