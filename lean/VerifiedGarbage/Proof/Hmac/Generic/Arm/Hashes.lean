import VerifiedGarbage.Proof.Hmac.Generic.Arm.Hash
import VerifiedGarbage.Proof.Sha256.Arm.Shared
import VerifiedGarbage.Proof.Sha1.Arm.Shared
import VerifiedGarbage.Proof.Md5.Arm.Shared
import VerifiedGarbage.Proof.Sha512.Arm.Shared
import VerifiedGarbage.Proof.Hmac.Generic.Common

/-!
# HMAC over any streaming hash function on 32-bit ARM: the hash functions

Untrusted: everything here is checked by Lean. `HashOK` for SHA-256, SHA-1,
MD5 and the SHA-512 family, from their own proofs, as on x86
(`Proof/Hmac/Generic/X86/Hashes.lean`). Their contracts are `initK`, `updK`
and `finK` at their sizes, but for the length bound of SHA-1's and MD5's
`finK`, and for SHA-256's and the SHA-512 family's, which hold from any initial hash
value.
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)
open VG.Proof.Hmac.Generic.Common (sha256_repr sha1_repr md5_repr sha512_repr finalHash_length)

/-! ## SHA-256 -/

def sha256H : Hash := ⟨64, 96, 32, 32, 20, "vg_sha256_init", Impl.Sha256.Arm.Stream.init,
  "vg_sha256_update", Impl.Sha256.Arm.Stream.update, "vg_sha256_finalize", Impl.Sha256.Arm.Stream.finalize⟩

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
  repr := sha256_repr
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

/-! ## SHA-1 -/

def sha1H : Hash := ⟨64, 84, 20, 20, 20, "vg_sha1_init", Impl.Sha1.Arm.Stream.init,
  "vg_sha1_update", Impl.Sha1.Arm.Stream.update, "vg_sha1_finalize", Impl.Sha1.Arm.Stream.finalize⟩

def sha1OK : HashOK sha1H where
  SH := Spec.Hmac.sha1S
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
  repr := sha1_repr
  init := Proof.Sha1.Arm.Stream.init_verified
  upd := Proof.Sha1.Arm.Stream.Update.update_verified
  fin := Proof.Sha1.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha1.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

/-! ## MD5 -/

def md5H : Hash := ⟨64, 80, 16, 16, 14, "vg_md5_init", Impl.Md5.Arm.Stream.init,
  "vg_md5_update", Impl.Md5.Arm.Stream.update, "vg_md5_finalize", Impl.Md5.Arm.Stream.finalize⟩

def md5OK : HashOK md5H where
  SH := Spec.Hmac.md5S
  Wb := 112
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
  repr := md5_repr
  init := Proof.Md5.Arm.Stream.init_verified
  upd := Proof.Md5.Arm.Stream.Update.update_verified
  fin := Proof.Md5.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

/-! ## The SHA-512 family -/

/-- The SHA-512 family member with initial hash value `iv` and a `D`-byte digest. -/
def sha512H (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨128, 192, D, 64, 34, initN, Impl.Sha512.Arm.Stream.init iv, "vg_sha512_update",
    Impl.Sha512.Arm.Stream.update, "vg_sha512_finalize", Impl.Sha512.Arm.Stream.finalize⟩

theorem sha512_updNF : Impl.Sha512.Arm.Stream.update.noFrames = true := by decide +kernel
theorem sha512_finNF : Impl.Sha512.Arm.Stream.finalize.noFrames = true := by decide +kernel

/-- `HashOK` for a member of the SHA-512 family, whose digest is the first
`D` bytes of the final hash value. -/
def sha512FamOK (SH : Spec.Hmac.StreamingHash) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue)
    (hS : SH.stateBytes = 192) (hD : SH.digestBytes = D) (hB : SH.H.blockSize = 128)
    (hR : SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hINF : (Impl.Sha512.Arm.Stream.init iv).noFrames = true) :
    HashOK (sha512H D initN iv) where
  SH := SH
  Wb := 272
  hS := hS
  hD := hD
  hB := hB
  hDF := hD64
  hF := Nat.le_refl 64
  hD0 := hD0
  hS0 := show 0 < 192 by decide
  hSB := show 192 ≤ 256 by decide
  hB0 := show 0 < 128 by decide
  hBB := Nat.le_refl 128
  hWb := show 272 ≤ 8 * 34 by decide
  hW := show 34 ≤ 64 by decide
  repr := hR ▸ sha512_repr iv
  init := hR ▸ Proof.Sha512.Arm.Stream.init_verified iv
  upd := hR ▸ Proof.Sha512.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha512.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := hINF
  updNF := sha512_updNF
  finNF := sha512_finNF

def sha384H : Hash := sha512H 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512H' : Hash := sha512H 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224H : Hash := sha512H 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256H : Hash := sha512H 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

def sha384OK : HashOK sha384H := sha512FamOK Spec.Hmac.sha384S 48 "vg_sha384_init" Spec.Sha512.H0_384
  rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)
def sha512OK : HashOK sha512H' := sha512FamOK Spec.Hmac.sha512S 64 "vg_sha512_init" Spec.Sha512.H0_512
  rfl rfl rfl rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (finalHash_length _ m))).symm) (by decide) (by decide)
  (by decide +kernel)
def sha512_224OK : HashOK sha512_224H := sha512FamOK Spec.Hmac.sha512_224S 28 "vg_sha512_224_init"
  Spec.Sha512.H0_512_224 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)
def sha512_256OK : HashOK sha512_256H := sha512FamOK Spec.Hmac.sha512_256S 32 "vg_sha512_256_init"
  Spec.Sha512.H0_512_256 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)

end VG.Proof.Hmac.Generic.Arm
