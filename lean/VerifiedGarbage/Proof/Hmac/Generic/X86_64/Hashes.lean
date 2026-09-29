import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha1.X86_64.Variant
import VerifiedGarbage.Proof.Md5.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.X86_64.Shared

/-!
# HMAC over any streaming hash function on x86-64: the hash functions

Untrusted: everything here is checked by Lean. `HashOK` for SHA-1, MD5 and
the SHA-512 family, from their own proofs; for SHA-1, for each implementation
`v` of its compression function (see `Proof/Sha1/X86_64/Variant.lean`), whose
`update` and `finalize` its HMAC and PBKDF2 then call.
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Proof.Hmac.Generic.Common (sha1_repr md5_repr sha512_repr finalHash_length)

/-- No instruction of `c` writes `rsp`, from a check that runs in the kernel. -/
theorem nosp_of {c : Prog isa} (h : ((instrs c).all fun i => !Taint.clobbers i .rsp) = true) : NoSp c :=
  fun i hi => by simpa using List.all_eq_true.mp h i hi

/-! ## SHA-1 -/

/-- SHA-1, with `update` and `finalize` calling the implementation `v` of the
compression function (named with its suffix, as `Generic/Sha1Compress/X86_64/Sha1.lean`
emits them). -/
def sha1H (v : Proof.Sha1.X86_64.Compress) : Hash := ⟨64, 84, 20, 20, 20, "vg_sha1_init",
  Impl.Sha1.X86_64.Stream.init, "vg_sha1_update" ++ v.suffix, Impl.Sha1.X86_64.Stream.update v.callee,
  "vg_sha1_finalize" ++ v.suffix, Impl.Sha1.X86_64.Stream.finalize v.callee⟩

/-- The parts of `sha1H v` that do not depend on `v`, as numbers or as those
of the scalar instance, which the kernel can evaluate. -/
theorem sha1H_B (v : Proof.Sha1.X86_64.Compress) : (sha1H v).B = 64 := rfl
theorem sha1H_S (v : Proof.Sha1.X86_64.Compress) : (sha1H v).S = 84 := rfl
theorem sha1H_D (v : Proof.Sha1.X86_64.Compress) : (sha1H v).D = 20 := rfl
theorem sha1H_F (v : Proof.Sha1.X86_64.Compress) : (sha1H v).F = 20 := rfl
theorem sha1H_buf (v : Proof.Sha1.X86_64.Compress) : (sha1H v).buf = 208 := rfl
theorem sha1H_initC (v : Proof.Sha1.X86_64.Compress) : (sha1H v).initC = Impl.Sha1.X86_64.Stream.init := rfl
theorem sha1H_initKeys (v : Proof.Sha1.X86_64.Compress) :
    (sha1H v).initKeys = (sha1H .scalar).initKeys := rfl
theorem sha1H_finPrologue (v : Proof.Sha1.X86_64.Compress) :
    (sha1H v).finPrologue = (sha1H .scalar).finPrologue := rfl
theorem sha1H_save (v : Proof.Sha1.X86_64.Compress) : (sha1H v).save = (sha1H .scalar).save := rfl
theorem sha1H_restore (v : Proof.Sha1.X86_64.Compress) : (sha1H v).restore = (sha1H .scalar).restore := rfl
theorem sha1H_updC (v : Proof.Sha1.X86_64.Compress) :
    (sha1H v).updC = Impl.Sha1.X86_64.Stream.update v.callee := rfl
theorem sha1H_finC (v : Proof.Sha1.X86_64.Compress) :
    (sha1H v).finC = Impl.Sha1.X86_64.Stream.finalize v.callee := rfl

def sha1OK (v : Proof.Sha1.X86_64.Compress) : HashOK (sha1H v) where
  SH := Spec.Hmac.sha1S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by simp only [sha1H]; decide
  hF := by simp only [sha1H]; decide
  hD0 := by simp only [sha1H]; decide
  hS0 := by simp only [sha1H]; decide
  hSB := by simp only [sha1H]; decide
  hB0 := by simp only [sha1H]; decide
  hBB := by simp only [sha1H]; decide
  hWb := by simp only [sha1H]; decide
  hW := by simp only [sha1H]; decide
  repr := sha1_repr
  init := Proof.Sha1.X86_64.Stream.init_verified
  upd := v.update_verified
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 20 (Spec.Sha1.bytesAt s'.mem _ 20) = _
        rw [List.take_of_length_le (by simp [Spec.Sha1.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := by simp only [sha1H]; decide +kernel
  updDepth := by simp only [sha1H, v.update_depth, Nat.le_refl]
  finDepth := by simp only [sha1H, v.finalize_depth, Nat.le_refl]
  initSp := nosp_of (by simp only [sha1H]; rw [← Code.allInstrs_eq]; decide +kernel)
  updSp := v.update_nosp
  finSp := v.finalize_nosp

/-! ## MD5 -/

def md5H : Hash := ⟨64, 80, 16, 16, 14, "vg_md5_init", Impl.Md5.X86_64.Stream.init,
  "vg_md5_update", Impl.Md5.X86_64.Stream.update, "vg_md5_finalize",
  Impl.Md5.X86_64.Stream.finalize⟩

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
  init := Proof.Md5.X86_64.Stream.init_verified
  upd := Proof.Md5.X86_64.Stream.Update.update_verified
  fin := Proof.Md5.X86_64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.X86_64.Stream.Finalize.finalize_verified.2.2 }
  initDepth := by decide +kernel
  updDepth := by decide +kernel
  finDepth := by decide +kernel
  initSp := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
  updSp := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
  finSp := nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)

/-! ## The SHA-512 family -/

/-- The SHA-512 family member with initial hash value `iv` and a `D`-byte digest. -/
def sha512H (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨128, 192, D, 64, 34, initN, Impl.Sha512.X86_64.Stream.init iv, "vg_sha512_update",
    Impl.Sha512.X86_64.Stream.update, "vg_sha512_finalize", Impl.Sha512.X86_64.Stream.finalize⟩

theorem sha512_upd_depth : Impl.Sha512.X86_64.Stream.update.depth ≤ 1 := by decide +kernel
theorem sha512_fin_depth : Impl.Sha512.X86_64.Stream.finalize.depth ≤ 1 := by decide +kernel
theorem sha512_upd_sp : NoSp Impl.Sha512.X86_64.Stream.update :=
  nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)
theorem sha512_fin_sp : NoSp Impl.Sha512.X86_64.Stream.finalize :=
  nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel)

/-- `HashOK` for a member of the SHA-512 family, whose digest is the first
`D` bytes of the final hash value. -/
def sha512FamOK (SH : Spec.Hmac.StreamingHash) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue)
    (hS : SH.stateBytes = 192) (hD : SH.digestBytes = D) (hB : SH.H.blockSize = 128)
    (hR : SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hID : (Impl.Sha512.X86_64.Stream.init iv).depth ≤ 1) (hISp : NoSp (Impl.Sha512.X86_64.Stream.init iv)) :
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
  init := hR ▸ Proof.Sha512.X86_64.Stream.init_verified iv
  upd := hR ▸ Proof.Sha512.X86_64.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.X86_64.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha512.X86_64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha512.X86_64.Stream.Finalize.finalize_verified.2.2 }
  initDepth := hID
  updDepth := sha512_upd_depth
  finDepth := sha512_fin_depth
  initSp := hISp
  updSp := sha512_upd_sp
  finSp := sha512_fin_sp

def sha384H : Hash := sha512H 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512H' : Hash := sha512H 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224H : Hash := sha512H 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256H : Hash := sha512H 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

def sha384OK : HashOK sha384H := sha512FamOK Spec.Hmac.sha384S 48 "vg_sha384_init" Spec.Sha512.H0_384
  rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide)
  (by decide +kernel) (nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel))
def sha512OK : HashOK sha512H' := sha512FamOK Spec.Hmac.sha512S 64 "vg_sha512_init" Spec.Sha512.H0_512
  rfl rfl rfl rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (finalHash_length _ m))).symm) (by decide) (by decide)
  (by decide +kernel) (nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel))
def sha512_224OK : HashOK sha512_224H := sha512FamOK Spec.Hmac.sha512_224S 28 "vg_sha512_224_init"
  Spec.Sha512.H0_512_224 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide)
  (by decide +kernel) (nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel))
def sha512_256OK : HashOK sha512_256H := sha512FamOK Spec.Hmac.sha512_256S 32 "vg_sha512_256_init"
  Spec.Sha512.H0_512_256 rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide)
  (by decide +kernel) (nosp_of (by rw [← Code.allInstrs_eq]; decide +kernel))

end VG.Proof.Hmac.Generic.X86_64
