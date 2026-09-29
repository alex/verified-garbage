import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hashes
import VerifiedGarbage.Proof.Sha1.AArch64.Shared
import VerifiedGarbage.Proof.Md5.AArch64.Shared
import VerifiedGarbage.Proof.Sha512.AArch64.Shared

/-!
# HMAC over any streaming hash function on AArch64: the hash functions

Untrusted: everything here is checked by Lean. `HashOK` for SHA-1, MD5 and
the SHA-512 family, from their own proofs. SHA-1's and MD5's contracts are
`initK`, `updK` and `finK` at their sizes (but for the length bound of
`finK`); the SHA-512 family's use no stack, so they imply ours, which let the
callee use 16 bytes below the stack pointer.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Proof.Hmac.Generic.X86_64 (sha1_repr md5_repr sha512_repr finalHash_length)

/-! ## SHA-1 -/

def sha1H : Hash := ⟨64, 84, 20, 20, 20, "vg_sha1_init", Impl.Sha1.AArch64.Stream.init,
  "vg_sha1_update", Impl.Sha1.AArch64.Stream.update, "vg_sha1_finalize",
  Impl.Sha1.AArch64.Stream.finalize⟩

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
  init := Proof.Sha1.AArch64.Stream.init_verified
  upd := Proof.Sha1.AArch64.Stream.Update.update_verified
  fin := Proof.Sha1.AArch64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha1.AArch64.Stream.Finalize.finalize_verified.2.2 }
  initDepth := by decide +kernel
  updDepth := by decide +kernel
  finDepth := by decide +kernel

/-! ## MD5 -/

def md5H : Hash := ⟨64, 80, 16, 16, 14, "vg_md5_init", Impl.Md5.AArch64.Stream.init,
  "vg_md5_update", Impl.Md5.AArch64.Stream.update, "vg_md5_finalize",
  Impl.Md5.AArch64.Stream.finalize⟩

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
  init := Proof.Md5.AArch64.Stream.init_verified
  upd := Proof.Md5.AArch64.Stream.Update.update_verified
  fin := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.2.2 }
  initDepth := by decide +kernel
  updDepth := by decide +kernel
  finDepth := by decide +kernel

/-! ## The SHA-512 family -/

/-- The SHA-512 family member with initial hash value `iv` and a `D`-byte digest. -/
def sha512H (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨128, 192, D, 64, 34, initN, Impl.Sha512.AArch64.Stream.init iv, "vg_sha512_update",
    Impl.Sha512.AArch64.Stream.update, "vg_sha512_finalize", Impl.Sha512.AArch64.Stream.finalize⟩

theorem sha512_upd_depth : Impl.Sha512.AArch64.Stream.update.fdepth ≤ 1 := by decide +kernel
theorem sha512_fin_depth : Impl.Sha512.AArch64.Stream.finalize.fdepth ≤ 1 := by decide +kernel

/-- A state satisfying `updK`'s precondition at the SHA-512 family's sizes. -/
def updSat : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 0⟩]
  wr := [⟨0x10000, 192⟩, ⟨0x40000, 224⟩]

/-- A state satisfying `finK`'s precondition at the SHA-512 family's sizes. -/
def finSat : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x20000 | .x3 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := []
  wr := [⟨0x10000, 192⟩, ⟨0x20000, 64⟩, ⟨0x40000, 224⟩]

theorem upd_sat (R : Mem → Addr → List Byte → Prop) : ∃ s, (updK 192 224 R).pre s := by
  refine ⟨updSat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩ <;>
    (intro a h₁ h₂; simp only [Region.Contains, updSat] at h₁ h₂; bv_omega)

theorem fin_sat (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) (D : Nat) :
    ∃ s, (finK 192 224 64 D R hash).pre s := by
  refine ⟨finSat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩ <;>
    (intro a h₁ h₂; simp only [Region.Contains, finSat] at h₁ h₂; bv_omega)

/-- `HashOK` for a member of the SHA-512 family, whose digest is the first
`D` bytes of the final hash value. -/
def sha512FamOK (SH : Spec.Hmac.StreamingHash) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue)
    (hS : SH.stateBytes = 192) (hD : SH.digestBytes = D) (hB : SH.H.blockSize = 128)
    (hR : SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hID : (Impl.Sha512.AArch64.Stream.init iv).fdepth ≤ 1) :
    HashOK (sha512H D initN iv) where
  SH := SH
  Wb := 224
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
  hWb := show 224 ≤ 8 * 34 by decide
  hW := show 34 ≤ 64 by decide
  repr := hR ▸ sha512_repr iv
  init := hR ▸ Proof.Sha512.AArch64.Stream.init_verified iv
  upd := hR ▸ Proof.Sha512.AArch64.Stream.Update.update_verified.of_implies
    { pre := fun _ ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := upd_sat _ }
  fin := Proof.Sha512.AArch64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := fin_sat _ _ _ }
  initDepth := hID
  updDepth := sha512_upd_depth
  finDepth := sha512_fin_depth

def sha384H : Hash := sha512H 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512H' : Hash := sha512H 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224H : Hash := sha512H 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256H : Hash := sha512H 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

def sha384OK : HashOK sha384H := sha512FamOK Spec.Hmac.sha384S 48 "vg_sha384_init" Spec.Sha512.H0_384
  rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)
def sha512OK : HashOK sha512H' := sha512FamOK Spec.Hmac.sha512S 64 "vg_sha512_init" Spec.Sha512.H0_512
  rfl rfl rfl rfl (fun m => (List.take_of_length_le (finalHash_length _ m).le).symm) (by decide) (by decide)
  (by decide +kernel)
def sha512_224OK : HashOK sha512_224H := sha512FamOK Spec.Hmac.sha512_224S 28 "vg_sha512_224_init"
  Spec.Sha512.H0_512_224 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)
def sha512_256OK : HashOK sha512_256H := sha512FamOK Spec.Hmac.sha512_256S 32 "vg_sha512_256_init"
  Spec.Sha512.H0_512_256 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide) (by decide +kernel)

end VG.Proof.Hmac.Generic.AArch64
