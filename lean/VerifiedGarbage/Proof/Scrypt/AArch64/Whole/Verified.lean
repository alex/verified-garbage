import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.CT
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Hashes.Sha256
import VerifiedGarbage.Proof.Framework.Contract

/-!
# scrypt on AArch64: the shared contract

Untrusted: everything here is checked by Lean. `vg_scrypt`, calling any
implementation of PBKDF2-HMAC-SHA256 verified against its shared contract
whose frames nest at most once, is verified against
`Spec.Scrypt.scryptContract` for the 96 bytes of stack its frames and calls
use (`scrypt_verified_of`); and so is the one calling the PBKDF2 made with
an implementation `c` of SHA-256's compression function (`scrypt_verified`).
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64

theorem map_range5 {α : Type} (f : Nat → α) :
    List.map f (List.range 5) = [f 0, f 1, f 2, f 3, f 4] := rfl

/-- A state satisfying the precondition: `N = 2`, `r = 1`, `p = 1`, a
one-byte key and an empty password and salt; the stack arguments are the
words at `0x90000`. -/
def satState : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x20000 | .x4 => 1 | .x5 => 0x30000 | .x6 => 1 | .x7 => 0x40000
    | _ => 0
  sp := 0x90000
  mem a := if a = 0x90000 then 2 else if a = 0x9000A then 5 else if a = 0x90010 then 17
    else if a = 0x9001A then 6 else if a = 0x90020 then 1 else 0
  rd := [⟨0x10000, 0⟩, ⟨0x20000, 0⟩, ⟨0x90000, 40⟩]
  wr := [⟨0x30000, 128⟩, ⟨0x40000, 256⟩, ⟨0x50000, 2176⟩, ⟨0x60000, 1⟩]

theorem scrypt_implies :
    Proof.Scrypt.scryptAArch64.Implies (Spec.Scrypt.scryptContract AArch64.abi 96) := by
  exact
    { pre := by
        intro s h
        -- Twice: the stack arguments' list evaluates only on the second pass.
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, map_range5, List.append_eq] at h
        sig_pre [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, map_range5, List.append_eq] at h
        sig_split h
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, map_range5, List.append_eq]
        sig_and_intros
        sig_close
        all_goals first
          | with_reducible assumption
          | with_reducible exact Region.Disjoint.symm ‹_›
      post := by
        rintro s s' - h
        sig_post [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, map_range5, List.append_eq]
        sig_reduce [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, map_range5, List.append_eq] at h
        exact h
      pub := by
        rintro s₁ s₂ - - h
        sig_pub [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, Proof.Scrypt.scryptAArch64,
          AArch64.abi, AArch64.argRegs, map_range5, List.append_eq] at h
        simp only [List.getD_cons_succ, List.getD_cons_zero] at h
        sig_split h
        rename_i hsp hlk h0 h1 h2 h3 h4 h5 h6 h7 a0 a1 a2 a3
        exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, a0, a1, a2, a3, h, hsp, hlk⟩
      sat := by
        sig_implies_sat [Spec.Scrypt.scryptContract, Spec.Scrypt.scryptSig, AArch64.abi, AArch64.argRegs,
          map_range5, List.append_eq, satState] [satState] using satState }

section
variable {pbk : Prog isa} (hv : Verified AArch64.target pbk (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16))
  (hd : pbk.aarch64Depth ≤ 1) (name : String)
include hv hd

/-- `vg_scrypt`, calling the implementation `pbk` of PBKDF2 named `name`. -/
theorem scrypt_verified_of :
    Verified AArch64.target (scrypt name pbk) (Spec.Scrypt.scryptContract AArch64.abi 96) :=
  Verified.of_correct (fun _ h => by
    obtain ⟨t, s', he, hp⟩ := scrypt_ok hv hd name h
    exact ⟨t, s', he, hp⟩) (scrypt_ct hv hd name) scrypt_implies

end

/-! ## With PBKDF2 made with an implementation of SHA-256's compression function -/

open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (hmacInit_fdepth hmacFin_fdepth iterate_fdepth)

/-- How deeply frames nest in `pbkdf2`. -/
theorem pbkdf2_fdepth {H : Hash} (hi : H.initC.aarch64Depth ≤ 1) (hu : H.updC.aarch64Depth ≤ 1)
    (hf : H.finC.aarch64Depth ≤ 1) (hc : H.compC.noFrames = true) : H.pbkdf2.aarch64Depth ≤ 1 := by
  have := hmacInit_fdepth hi hu
  have := hmacFin_fdepth hf
  have := iterate_fdepth hc
  simp only [Hash.pbkdf2, Hash.key, Hash.hashKey, Hash.setup, Hash.block, Hash.outLen, Hash.outLoop,
    Code.aarch64Depth]
  omega

variable (c : Proof.Sha256.AArch64.Compress)

/-- PBKDF2-HMAC-SHA256 made with `c`. -/
abbrev pbkOf : Prog isa := (Proof.Pbkdf2.Md.AArch64.Sha256.hash c).pbkdf2

/-- Its name. -/
abbrev pbkName : String := Spec.Hmac.sha256I.pbkdf2Api.name ++ c.suffix

theorem pbk_verified :
    Verified AArch64.target (pbkOf c) (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16) :=
  (Proof.Pbkdf2.Md.AArch64.Sha256.variant c).pbkdf2

theorem pbk_depth : (pbkOf c).aarch64Depth ≤ 1 :=
  pbkdf2_fdepth (Proof.Pbkdf2.Md.AArch64.Sha256.streamOK c).initDepth
    (Proof.Pbkdf2.Md.AArch64.Sha256.streamOK c).updDepth (Proof.Pbkdf2.Md.AArch64.Sha256.streamOK c).finDepth
    c.noFrames

/-- `vg_scrypt` made with `c`. -/
theorem scrypt_verified :
    Verified AArch64.target (scrypt (pbkName c) (pbkOf c)) (Spec.Scrypt.scryptContract AArch64.abi 96) :=
  scrypt_verified_of (pbk_verified c) (pbk_depth c) (pbkName c)

end VG.Proof.Scrypt.AArch64.Whole
