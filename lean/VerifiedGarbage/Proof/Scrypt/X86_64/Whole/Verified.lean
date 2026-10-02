import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.CT
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.Contract

/-!
# scrypt on x86-64: the shared contract

`vg_scrypt`, calling any implementation of PBKDF2-HMAC-SHA256 verified against
its shared contract, is verified against `Spec.Scrypt.scryptContract` for the
88 bytes of stack its frame and calls use (`scrypt_verified_of`); for the
PBKDF2 made with an implementation `c` of SHA-256's compression function
(`scrypt_verified`), whose code never writes `rsp` but by the frame
(`scrypt_spSafe`).
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Pbkdf2.Md.X86_64 (core core_pbkdf2 nosp_of)

theorem map_range7 {α : Type} (f : Nat → α) :
    List.map f (List.range 7) = [f 0, f 1, f 2, f 3, f 4, f 5, f 6] := rfl

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
bytes at `0x90008`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x10000 | .rdx => 0x20000 | .r8 => 1 | .r9 => 0x30000 | .rsp => 0x90000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x90008 then 1 else if a = 0x90012 then 4 else if a = 0x90018 then 2
    else if a = 0x90022 then 5 else if a = 0x90028 then 17 else if a = 0x90032 then 6
    else if a = 0x90038 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90008, 56⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptX86_64.Implies (Spec.Scrypt.scryptContract X86_64.abi 88) := by
  exact
    { pre := by
        intro s h
        -- Twice: the stack arguments' list evaluates only on the second pass.
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64, X86_64.abi,
          X86_64.argRegs, map_range7, List.append_eq] at h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64, X86_64.abi,
          X86_64.argRegs, map_range7, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64, X86_64.abi,
          X86_64.argRegs, map_range7, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, map_range7, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, map_range7, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptX86_64,
          X86_64.abi, X86_64.argRegs, map_range7, List.append_eq] at h
        simp only [List.getD_cons_succ, List.getD_cons_zero] at h
        sig_split h
        rename_i hrsp hlk h1 h2 h3 h4 h5 h6 a0 a1 a2 a3 a4 a5
        exact ⟨h1, h2, h3, h4, h5, h6, a0, a1, a2, a3, a4, a5, h, hrsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, X86_64.abi, X86_64.argRegs,
          map_range7, List.append_eq, satState] [satState] using satState }

section
variable {pbk : Prog isa} (hv : Verified X86_64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24))
  (hsp : NoSp pbk) (hd : pbk.depth ≤ 3) (name : String)
include hv hsp hd

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`, if
no instruction of it (or of the functions it calls) loads MXCSR. -/
theorem scrypt_verified_of (hmx : (scrypt name pbk).allInstrs (fun i => !loadsMxcsr i) = true) :
    Verified X86_64.target (scrypt name pbk) (Spec.Scrypt.scryptContract X86_64.abi 88) :=
  Verified.of_correct (scrypt_correct hv hsp hd name hmx) (scrypt_ct hv hsp hd name) scrypt_implies

end

/-! ## With PBKDF2 made with an implementation of SHA-256's compression function -/

open VG.Impl.Pbkdf2.Md.X86_64 (Hash)

/-- How deeply calls nest in `pbkdf2`, from its own code. -/
theorem core_pbkdf2_depth {H : Hash} (hc : H.compC.depth = 0) (hi : H.initC.depth = 0)
    (h : (core H).pbkdf2.depth ≤ 3) : H.pbkdf2.depth ≤ 3 := by
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Hash.hmacInit, Hash.hmacFin, Hash.iterate, Impl.Pbkdf2.X86_64.iterate, Impl.Pbkdf2.X86_64.body,
    Impl.Pbkdf2.X86_64.compressBlock, Hash.updC, Hash.finC, Hash.stream,
    Impl.Hmac.Generic.X86_64.Hash.init,
    Impl.Hmac.Generic.X86_64.Hash.callInit, Impl.Hmac.Generic.X86_64.Hash.callUpd,
    Impl.Hmac.Generic.X86_64.Hash.callFin,
    Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody, Impl.MdStream.X86_64.updateTail,
    Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Impl.MdStream.X86_64.finalize, Impl.MdStream.X86_64.finalizeBody,
    core, Code.depth, hc, hi] at h ⊢
  exact h

variable (c : Proof.Sha256.X86_64.Compress)

/-- PBKDF2-HMAC-SHA256 made with `c`. -/
abbrev pbkOf : Prog isa := (Proof.Pbkdf2.Md.X86_64.Sha256.hash c).pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2Api.name ++ c.suffix

theorem pbk_verified :
    Verified X86_64.target (pbkOf c) (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24) :=
  (Proof.Pbkdf2.Md.X86_64.Sha256.variant c).pbkdf2

theorem pbk_nosp : NoSp (pbkOf c) :=
  nosp_of (core_pbkdf2 (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cNs
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iNs
    (by decide +kernel : Proof.Pbkdf2.Md.X86_64.Sha256.coreH.pbkdf2.allInstrs
      (fun i => !Taint.clobbers i .rsp) = true))

theorem pbk_depth : (pbkOf c).depth ≤ 3 :=
  core_pbkdf2_depth (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cD
    (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iD
    (by decide +kernel : Proof.Pbkdf2.Md.X86_64.Sha256.coreH.pbkdf2.depth ≤ 3)

theorem pbk_mx : (pbkOf c).allInstrs (fun i => !loadsMxcsr i) = true :=
  core_pbkdf2 (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).cMx (Proof.Pbkdf2.Md.X86_64.Sha256.callees c).iMx
    Proof.Pbkdf2.Md.X86_64.Sha256.coreOK.pbkMx

theorem scrypt_mx : (scrypt (pbkName c) (pbkOf c)).allInstrs (fun i => !loadsMxcsr i) = true := by
  have hr : Impl.Scrypt.X86_64.roMix.allInstrs (fun i => !loadsMxcsr i) = true := by lit_decide
  simp only [scrypt, scryptBody, pbkCall, romixLoop, Code.allInstrs, pbk_mx c, hr, Bool.and_true,
    Bool.true_and]
  decide

/-- `vg_scrypt` made with `c`. -/
theorem scrypt_verified :
    Verified X86_64.target (scrypt (pbkName c) (pbkOf c)) (Spec.Scrypt.scryptContract X86_64.abi 88) :=
  scrypt_verified_of (pbk_verified c) (pbk_nosp c) (pbk_depth c) (pbkName c) (scrypt_mx c)

/-- No instruction writes `rsp` but the frame's push and pop. -/
theorem scrypt_spSafe : (scrypt (pbkName c) (pbkOf c)).all (fun i => !isa.writesSp i) = true := by
  have hp : (pbkOf c).all (fun i => !isa.writesSp i) = true :=
    (Proof.Pbkdf2.Md.X86_64.Sha256.variant c).pbkdf2Sp
  have hr : Impl.Scrypt.X86_64.roMix.all (fun i => !isa.writesSp i) = true :=
    Code.all_of_allInstrs (by lit_decide)
  simp only [scrypt, scryptBody, pbkCall, romixLoop, Code.all, hp, hr, Bool.and_true, Bool.true_and]
  decide

end VG.Proof.Scrypt.X86_64.Whole
