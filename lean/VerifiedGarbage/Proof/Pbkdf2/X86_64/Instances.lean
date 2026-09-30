import VerifiedGarbage.Proof.Pbkdf2.X86_64.IterateCT
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Lit
import VerifiedGarbage.Proof.Sha1.X86_64.Variant
import VerifiedGarbage.Proof.Sha256.X86_64.Variant
import VerifiedGarbage.Proof.Md5.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sha512.X86_64.Variant
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Spec.Pbkdf2.Contract

/-!
# PBKDF2-HMAC's iteration on x86-64: the hash functions

Untrusted: everything here is checked by Lean. The generic proof
(`Iterate.lean`, `IterateCT.lean`) at every hash function whose streaming
code is the generic one of `Impl/MdStream/X86_64.lean` (MD5, SHA-1, SHA-256
and the SHA-512 family), moved to the shared contracts of `Spec/`, which the
artifacts are emitted with. For SHA-1, SHA-256 and the SHA-512 family, it
holds for every implementation `v` of the compression function (a variant of
`Sha1Compress`, `Sha256Compress` or `Sha512Compress`): the checks do not look
into the compression function.
-/

namespace VG.Proof.Pbkdf2.X86_64.Instances

open VG VG.X86_64
open VG.Impl.Pbkdf2.X86_64 (iterate)
open VG.Proof.Pbkdf2.X86_64
open VG.Proof.Hmac.Generic.Common (readW_reloc)

/-! ## SHA-1 -/

theorem sha1_reloc : Proof.Sha1.md.Reloc := fun _ _ _ _ h => by
  apply Vector.ext
  intro j hj
  simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
  exact readW_reloc h (by omega)

theorem sha1_ok : HashOk Impl.Sha1.X86_64.Stream.params 20 56 Spec.Hmac.sha1S Proof.Sha1.md Spec.Sha1.H0 where
  sizes := ⟨Proof.Sha1.X86_64.Stream.dims, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Sha1.X86_64.Stream.shape
  reloc := sha1_reloc
  lenOk := trivial
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h,
    fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm, by decide, by decide⟩

theorem sha1_checks : Checks Impl.Sha1.X86_64.Stream.params 20 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha1_imp : (iterK Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract X86_64.abi 8) :=
  iterImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1,
      X86_64.abi, X86_64.argRegs] using iterSat 84 20 56)

/-- The iteration calling the implementation `v` of the compression function. -/
abbrev sha1Iterate (v : Proof.Sha1.X86_64.Compress) : Prog isa :=
  iterate Impl.Sha1.X86_64.Stream.params 20 v.callee.name v.callee.code

theorem sha1_mx (v : Proof.Sha1.X86_64.Compress) :
    (sha1Iterate v).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sha1Iterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, v.mxcsr, Bool.and_true,
    Bool.true_and]
  decide +kernel

theorem sha1_sp (v : Proof.Sha1.X86_64.Compress) :
    (sha1Iterate v).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sha1Iterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

theorem sha1 (v : Proof.Sha1.X86_64.Compress) :
    Verified X86_64.target (sha1Iterate v) (Spec.Hmac.sha1I.iterateContract X86_64.abi 8) :=
  (verified sha1_ok sha1_checks v.ok (sha1_mx v) sha1_imp.sat_left).of_implies sha1_imp

/-! ## SHA-256 -/

theorem sha256_reloc : Proof.Sha256.md.Reloc := fun _ _ _ _ h =>
  Proof.Hmac.Common.stateAt_eq_of_bytes h

theorem sha256_ok :
    HashOk Impl.Sha256.X86_64.Stream.params 32 104 Spec.Hmac.sha256S Proof.Sha256.md Spec.Sha256.H0 where
  sizes := ⟨Proof.Sha256.X86_64.Stream.dims, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Sha256.X86_64.Stream.shape
  reloc := sha256_reloc
  lenOk := trivial
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h,
    fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm, by decide, by decide⟩

theorem sha256_checks : Checks Impl.Sha256.X86_64.Stream.params 32 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha256_imp : (iterK Spec.Hmac.sha256S 104).Implies (Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8) := by
  sig_implies [Spec.Pbkdf2.iterateSha256Contract, Spec.Pbkdf2.iterateSha256Sig, iterK, Spec.Hmac.sha256S,
    Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] [iterSat] using iterSat 96 32 104

/-- The iteration calling the implementation `v` of the compression function. -/
abbrev sha256Iterate (v : Proof.Sha256.X86_64.Compress) : Prog isa :=
  iterate Impl.Sha256.X86_64.Stream.params 32 v.callee.name v.callee.code

theorem sha256_mx (v : Proof.Sha256.X86_64.Compress) :
    (sha256Iterate v).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sha256Iterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, v.mxcsr, Bool.and_true,
    Bool.true_and]
  decide +kernel

theorem sha256_sp (v : Proof.Sha256.X86_64.Compress) :
    (sha256Iterate v).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sha256Iterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

theorem sha256 (v : Proof.Sha256.X86_64.Compress) :
    Verified X86_64.target (sha256Iterate v) (Spec.Pbkdf2.iterateSha256Contract X86_64.abi 8) :=
  (verified sha256_ok sha256_checks (Proof.Sha256.X86_64.Stream.callee v.ok) (sha256_mx v)
    sha256_imp.sat_left).of_implies sha256_imp

/-! ## MD5 -/

theorem md5_reloc : Proof.Md5.md.Reloc := fun _ _ _ _ h => by
  apply Vector.ext
  intro j hj
  simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
  exact readW_reloc h (by omega)

theorem md5_ok : HashOk Impl.Md5.X86_64.Stream.params 16 48 Spec.Hmac.md5S Proof.Md5.md Spec.Md5.H0 where
  sizes := ⟨Proof.Md5.X86_64.Stream.dims, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  shape := Proof.Md5.X86_64.Stream.shape
  reloc := md5_reloc
  lenOk := trivial
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h,
    fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm, by decide, by decide⟩

theorem md5_checks : Checks Impl.Md5.X86_64.Stream.params 16 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem md5_imp : (iterK Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract X86_64.abi 8) :=
  iterImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5,
      X86_64.abi, X86_64.argRegs] using iterSat 80 16 48)

theorem md5 :
    Verified X86_64.target (iterate Impl.Md5.X86_64.Stream.params 16 "vg_md5_compress" Impl.Md5.X86_64.compress)
      (Spec.Hmac.md5I.iterateContract X86_64.abi 8) :=
  (verified md5_ok md5_checks (name := "vg_md5_compress") Proof.Md5.X86_64.Stream.callee (by lit_decide) md5_imp.sat_left).of_implies md5_imp

/-! ## The SHA-512 family -/

theorem sha512_reloc : Proof.Sha512.md.Reloc := fun _ _ _ _ h => by
  apply Vector.ext
  intro j hj
  simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
  exact readW_reloc h (by omega)

/-- A member of the SHA-512 family, whose digest is the first `D` bytes of the
final hash value, from its initial hash value `iv`. -/
theorem sha512Fam_ok (S : Spec.Hmac.StreamingHash) (D : Nat) (iv : Spec.Sha512.HashValue)
    (hB : S.H.blockSize = 128) (hS : S.stateBytes = 192) (hD : S.digestBytes = D)
    (hR : S.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hsz : Sizes Impl.Sha512.X86_64.Stream.params D 234) :
    HashOk Impl.Sha512.X86_64.Stream.params D 234 S Proof.Sha512.md iv where
  sizes := hsz
  shape := Proof.Sha512.X86_64.Stream.shape
  reloc := sha512_reloc
  lenOk := show 128 + D < 2 ^ 64 by have := hsz.DN; simp [Impl.Sha512.X86_64.Stream.params] at this; omega
  link := ⟨hB, hS, hD, fun _ _ _ h => by rw [hR] at h; exact h, hh, hsz.DN,
    by have := hsz.pad; simp [Impl.Sha512.X86_64.Stream.params] at this ⊢; omega⟩

theorem sha512Fam_sizes {D : Nat} (h₁ : D % 4 = 0) (h₂ : 0 < D) (h₃ : D ≤ 64) :
    Sizes Impl.Sha512.X86_64.Stream.params D 234 :=
  ⟨Proof.Sha512.X86_64.Stream.dims, by decide, h₁, by decide, h₂, h₃, by decide,
    by simp [Impl.Sha512.X86_64.Stream.params]; omega, by decide, by decide⟩

theorem sha384_checks : Checks Impl.Sha512.X86_64.Stream.params 48 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_checks : Checks Impl.Sha512.X86_64.Stream.params 64 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_224_checks : Checks Impl.Sha512.X86_64.Stream.params 28 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_256_checks : Checks Impl.Sha512.X86_64.Stream.params 32 :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha384_imp : (iterK Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract X86_64.abi 8) :=
  iterImp Spec.Hmac.sha384S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384,
      X86_64.abi, X86_64.argRegs] using iterSat 192 48 234)

theorem sha512_imp : (iterK Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract X86_64.abi 8) :=
  iterImp Spec.Hmac.sha512S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512,
      X86_64.abi, X86_64.argRegs] using iterSat 192 64 234)

theorem sha512_224_imp :
    (iterK Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.iterateContract X86_64.abi 8) :=
  iterImp Spec.Hmac.sha512_224S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224,
      X86_64.abi, X86_64.argRegs] using iterSat 192 28 234)

theorem sha512_256_imp :
    (iterK Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract X86_64.abi 8) :=
  iterImp Spec.Hmac.sha512_256S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256,
      X86_64.abi, X86_64.argRegs] using iterSat 192 32 234)

/-- The iteration with a `D`-byte digest, calling the implementation `v` of
the compression function. -/
abbrev sha512FamIterate (v : Proof.Sha512.X86_64.Compress) (D : Nat) : Prog isa :=
  iterate Impl.Sha512.X86_64.Stream.params D v.callee.name v.callee.code

abbrev sha384Iterate (v : Proof.Sha512.X86_64.Compress) : Prog isa := sha512FamIterate v 48
abbrev sha512Iterate (v : Proof.Sha512.X86_64.Compress) : Prog isa := sha512FamIterate v 64
abbrev sha512_224Iterate (v : Proof.Sha512.X86_64.Compress) : Prog isa := sha512FamIterate v 28
abbrev sha512_256Iterate (v : Proof.Sha512.X86_64.Compress) : Prog isa := sha512FamIterate v 32

theorem sha384_mx (v : Proof.Sha512.X86_64.Compress) :
    (sha384Iterate v).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sha384Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, v.mxcsr, Bool.and_true,
    Bool.true_and]
  decide +kernel

theorem sha384_sp (v : Proof.Sha512.X86_64.Compress) :
    (sha384Iterate v).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sha384Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

theorem sha512_mx (v : Proof.Sha512.X86_64.Compress) :
    (sha512Iterate v).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sha512Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, v.mxcsr, Bool.and_true,
    Bool.true_and]
  decide +kernel

theorem sha512_sp (v : Proof.Sha512.X86_64.Compress) :
    (sha512Iterate v).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sha512Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

theorem sha512_224_mx (v : Proof.Sha512.X86_64.Compress) :
    (sha512_224Iterate v).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sha512_224Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, v.mxcsr, Bool.and_true,
    Bool.true_and]
  decide +kernel

theorem sha512_224_sp (v : Proof.Sha512.X86_64.Compress) :
    (sha512_224Iterate v).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sha512_224Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

theorem sha512_256_mx (v : Proof.Sha512.X86_64.Compress) :
    (sha512_256Iterate v).allInstrs (fun i => !loadsMxcsr i) = true := by
  simp only [sha512_256Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.allInstrs, v.mxcsr, Bool.and_true,
    Bool.true_and]
  decide +kernel

theorem sha512_256_sp (v : Proof.Sha512.X86_64.Compress) :
    (sha512_256Iterate v).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [sha512_256Iterate, sha512FamIterate, iterate, Impl.Pbkdf2.X86_64.body, Impl.Pbkdf2.X86_64.compressBlock,
    Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith, Code.all, v.spSafe, Bool.true_and]
  decide +kernel

theorem sha384 (v : Proof.Sha512.X86_64.Compress) :
    Verified X86_64.target (sha384Iterate v) (Spec.Hmac.sha384I.iterateContract X86_64.abi 8) :=
  (verified (sha512Fam_ok Spec.Hmac.sha384S 48 Spec.Sha512.H0_384 rfl rfl rfl rfl (fun _ => rfl)
    (sha512Fam_sizes (by decide) (by decide) (by decide))) sha384_checks v.ok
    (sha384_mx v) sha384_imp.sat_left).of_implies sha384_imp

theorem sha512 (v : Proof.Sha512.X86_64.Compress) :
    Verified X86_64.target (sha512Iterate v) (Spec.Hmac.sha512I.iterateContract X86_64.abi 8) :=
  (verified (sha512Fam_ok Spec.Hmac.sha512S 64 Spec.Sha512.H0_512 rfl rfl rfl rfl
    (fun m => (List.take_of_length_le (Nat.le_of_eq (Proof.Hmac.Generic.Common.finalHash_length _ m))).symm)
    (sha512Fam_sizes (by decide) (by decide) (by decide))) sha512_checks v.ok
    (sha512_mx v) sha512_imp.sat_left).of_implies sha512_imp

theorem sha512_224 (v : Proof.Sha512.X86_64.Compress) :
    Verified X86_64.target (sha512_224Iterate v) (Spec.Hmac.sha512_224I.iterateContract X86_64.abi 8) :=
  (verified (sha512Fam_ok Spec.Hmac.sha512_224S 28 Spec.Sha512.H0_512_224 rfl rfl rfl rfl (fun _ => rfl)
    (sha512Fam_sizes (by decide) (by decide) (by decide))) sha512_224_checks v.ok
    (sha512_224_mx v) sha512_224_imp.sat_left).of_implies sha512_224_imp

theorem sha512_256 (v : Proof.Sha512.X86_64.Compress) :
    Verified X86_64.target (sha512_256Iterate v) (Spec.Hmac.sha512_256I.iterateContract X86_64.abi 8) :=
  (verified (sha512Fam_ok Spec.Hmac.sha512_256S 32 Spec.Sha512.H0_512_256 rfl rfl rfl rfl (fun _ => rfl)
    (sha512Fam_sizes (by decide) (by decide) (by decide))) sha512_256_checks v.ok
    (sha512_256_mx v) sha512_256_imp.sat_left).of_implies sha512_256_imp

end VG.Proof.Pbkdf2.X86_64.Instances
