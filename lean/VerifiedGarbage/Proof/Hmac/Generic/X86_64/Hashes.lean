import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Hash
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Sha1.X86_64.Shared
import VerifiedGarbage.Proof.Sha1.X86_64.Variant
import VerifiedGarbage.Proof.Md5.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.X86_64.Variant

/-!
# HMAC over any streaming hash function on x86-64: the hash functions

Untrusted: everything here is checked by Lean. `HashOK` for SHA-1, MD5 and
the SHA-512 family, from their own proofs; for SHA-1 and the SHA-512 family,
for each implementation `v` of their compression function (see
`Proof/Sha1/X86_64/Variant.lean` and `Proof/Sha512/X86_64/Variant.lean`),
whose `update` and `finalize` their HMAC then calls.
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

/-- The parts of a `Hash` that depend only on its sizes. -/
theorem Hash.initKeys_congr {H H' : Hash} (hB : H.B = H'.B) (hW : H.W = H'.W) :
    H.initKeys = H'.initKeys := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hW; subst hB hW; rfl

theorem Hash.finPrologue_congr {H H' : Hash} (hW : H.W = H'.W) : H.finPrologue = H'.finPrologue := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hW; subst hW; rfl

theorem Hash.save_congr {H H' : Hash} (hW : H.W = H'.W) : H.save = H'.save := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hW; subst hW; rfl

theorem Hash.restore_congr {H H' : Hash} (hW : H.W = H'.W) : H.restore = H'.restore := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hW; subst hW; rfl

/- These are rewrites, not definitional lemmas: `simp` then adds their proofs,
rather than leaving the kernel to unfold `sha1H v` against `sha1H .scalar`. -/
theorem sha1H_initKeys (v : Proof.Sha1.X86_64.Compress) :
    (sha1H v).initKeys = (sha1H .scalar).initKeys := Hash.initKeys_congr rfl rfl
theorem sha1H_finPrologue (v : Proof.Sha1.X86_64.Compress) :
    (sha1H v).finPrologue = (sha1H .scalar).finPrologue := Hash.finPrologue_congr rfl
theorem sha1H_save (v : Proof.Sha1.X86_64.Compress) : (sha1H v).save = (sha1H .scalar).save :=
  Hash.save_congr rfl
theorem sha1H_restore (v : Proof.Sha1.X86_64.Compress) : (sha1H v).restore = (sha1H .scalar).restore :=
  Hash.restore_congr rfl

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
  initDepth := by simp only [sha1H]; lit_decide
  updDepth := by simp only [sha1H, v.update_depth, Nat.le_refl]
  finDepth := by simp only [sha1H, v.finalize_depth, Nat.le_refl]
  initSp := nosp_of (by simp only [sha1H]; rw [← Code.allInstrs_eq]; lit_decide)
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
  initDepth := by lit_decide
  updDepth := by lit_decide
  finDepth := by lit_decide
  initSp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  updSp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)
  finSp := nosp_of (by rw [← Code.allInstrs_eq]; lit_decide)

/-! ## The SHA-512 family -/

/-- The SHA-512 family member with initial hash value `iv` and a `D`-byte
digest, with `update` and `finalize` calling the implementation `v` of the
compression function (named with its suffix, as
`Generic/Sha512Compress/X86_64/Sha512.lean` emits them). -/
def sha512H (v : Proof.Sha512.X86_64.Compress) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) :
    Hash :=
  ⟨128, 192, D, 64, 34, initN, Impl.Sha512.X86_64.Stream.init iv, "vg_sha512_update" ++ v.suffix,
    Impl.Sha512.X86_64.Stream.update v.callee, "vg_sha512_finalize" ++ v.suffix,
    Impl.Sha512.X86_64.Stream.finalize v.callee⟩

def sha384H (v : Proof.Sha512.X86_64.Compress) : Hash := sha512H v 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512H' (v : Proof.Sha512.X86_64.Compress) : Hash := sha512H v 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224H (v : Proof.Sha512.X86_64.Compress) : Hash :=
  sha512H v 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256H (v : Proof.Sha512.X86_64.Compress) : Hash :=
  sha512H v 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

section
variable (v : Proof.Sha512.X86_64.Compress) (D : Nat) (n : String) (iv : Spec.Sha512.HashValue)

/-- The parts of `sha512H v D n iv` that do not depend on `v`, as numbers or
as those of the scalar SHA-384 instance, which the kernel can evaluate. -/
theorem sha512H_B : (sha512H v D n iv).B = 128 := rfl
theorem sha512H_S : (sha512H v D n iv).S = 192 := rfl
theorem sha512H_D : (sha512H v D n iv).D = D := rfl
theorem sha512H_F : (sha512H v D n iv).F = 64 := rfl
theorem sha512H_buf : (sha512H v D n iv).buf = 320 := rfl
theorem sha512H_initC : (sha512H v D n iv).initC = Impl.Sha512.X86_64.Stream.init iv := rfl

/- These are rewrites, not definitional lemmas: `simp` then adds their proofs,
rather than leaving the kernel to unfold `sha512H v D n iv` against
`sha384H .scalar`. -/
theorem sha512H_initKeys : (sha512H v D n iv).initKeys = (sha384H .scalar).initKeys :=
  Hash.initKeys_congr rfl rfl
theorem sha512H_finPrologue : (sha512H v D n iv).finPrologue = (sha384H .scalar).finPrologue :=
  Hash.finPrologue_congr rfl
theorem sha512H_save : (sha512H v D n iv).save = (sha384H .scalar).save := Hash.save_congr rfl
theorem sha512H_restore : (sha512H v D n iv).restore = (sha384H .scalar).restore := Hash.restore_congr rfl

theorem sha512H_updC : (sha512H v D n iv).updC = Impl.Sha512.X86_64.Stream.update v.callee := rfl
theorem sha512H_finC : (sha512H v D n iv).finC = Impl.Sha512.X86_64.Stream.finalize v.callee := rfl

end

/-- `HashOK` for a member of the SHA-512 family, whose digest is the first
`D` bytes of the final hash value, for any implementation `v` of the
compression function. -/
def sha512FamOK (v : Proof.Sha512.X86_64.Compress) (SH : Spec.Hmac.StreamingHash) (D : Nat) (initN : String)
    (iv : Spec.Sha512.HashValue)
    (hS : SH.stateBytes = 192) (hD : SH.digestBytes = D) (hB : SH.H.blockSize = 128)
    (hR : SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hD0 : 0 < D) (hD64 : D ≤ 64)
    (hID : (Impl.Sha512.X86_64.Stream.init iv).depth ≤ 1) (hISp : NoSp (Impl.Sha512.X86_64.Stream.init iv)) :
    HashOK (sha512H v D initN iv) where
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
  upd := hR ▸ v.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.update_verified.2.2 }
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := hID
  updDepth := Nat.le_of_eq v.update_depth
  finDepth := Nat.le_of_eq v.finalize_depth
  initSp := hISp
  updSp := v.update_nosp
  finSp := v.finalize_nosp

def sha384OK (v : Proof.Sha512.X86_64.Compress) : HashOK (sha384H v) :=
  sha512FamOK v Spec.Hmac.sha384S 48 "vg_sha384_init" Spec.Sha512.H0_384
    rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide)
    (by lit_decide) (nosp_of (by rw [← Code.allInstrs_eq]; lit_decide))
def sha512OK (v : Proof.Sha512.X86_64.Compress) : HashOK (sha512H' v) :=
  sha512FamOK v Spec.Hmac.sha512S 64 "vg_sha512_init" Spec.Sha512.H0_512
    rfl rfl rfl rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (finalHash_length _ m))).symm)
    (by decide) (by decide)
    (by lit_decide) (nosp_of (by rw [← Code.allInstrs_eq]; lit_decide))
def sha512_224OK (v : Proof.Sha512.X86_64.Compress) : HashOK (sha512_224H v) :=
  sha512FamOK v Spec.Hmac.sha512_224S 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
    rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide)
    (by lit_decide) (nosp_of (by rw [← Code.allInstrs_eq]; lit_decide))
def sha512_256OK (v : Proof.Sha512.X86_64.Compress) : HashOK (sha512_256H v) :=
  sha512FamOK v Spec.Hmac.sha512_256S 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256
    rfl rfl rfl rfl (fun _ => rfl) (by decide) (by decide)
    (by lit_decide) (nosp_of (by rw [← Code.allInstrs_eq]; lit_decide))

end VG.Proof.Hmac.Generic.X86_64
