import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Block
import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hashes
import VerifiedGarbage.Proof.Sha512.Md
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize

/-!
# HMAC and PBKDF2-HMAC on x86 (32-bit): the Merkle–Damgård hash functions

MD5, SHA-1 and the SHA-512 family as `Hash`es of `Impl/Pbkdf2/Md/X86.lean`:
their streaming functions (`Proof/Pbkdf2/Stream/X86/Hashes.lean`), their
compression functions and the code writing their digests
(the `out` of their `Impl.MdStream.X86` parameters), and what the proofs know
of them (`MdOk`), from their own proofs: the `Md` of the generic streaming
proofs (`Proof/Md5/Md.lean` and the others), the digests their code writes
(from their `Shape`s), and their compression functions' contracts, which are
`cmpK`. SHA-256, whose compression function has a
variant for each backend on x86, is in `Sha256.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.X86

open VG.X86
open VG.Impl.Pbkdf2.Md.X86 (Hash)
open VG.Proof.MdStream (Md)
open VG.Proof.Pbkdf2.Stream.X86 (md5H sha1H sha512H md5OK sha1OK sha384OK sha512OK sha512_224OK sha512_256OK)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_nil writeBytes_append writeBytes_frame)

/-! ## The hash functions -/

/-- MD5: a 16-byte hash value, a little-endian length field and digest. -/
def md5M : Hash :=
  ⟨md5H, 16, 8, false, 64, "vg_md5_compress", Impl.Md5.X86.compress, Impl.Md5.X86.Stream.params.out⟩

/-- SHA-1: a 20-byte hash value, a big-endian length field and digest. -/
def sha1M : Hash :=
  ⟨sha1H, 20, 8, true, 112, "vg_sha1_compress", Impl.Sha1.X86.compress, Impl.Sha1.X86.Stream.params.out⟩

/-- The member of the SHA-512 family with a `D`-byte digest and initial hash
value `iv`: a 64-byte hash value, a big-endian 16-byte length field, and the
digest of the whole hash value (`D` bytes of which are output). -/
def sha512M (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash :=
  ⟨sha512H D initN iv, 64, 16, true, 224, "vg_sha512_compress", Impl.Sha512.X86.compress,
    Impl.Sha512.X86.Stream.params.out⟩

def sha384M : Hash := sha512M 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512M' : Hash := sha512M 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224M : Hash := sha512M 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256M : Hash := sha512M 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

/-! ## What the proofs know of them -/

/-- The weaker register guarantee `OutOk` asks of `Impl.MdStream.X86`'s
`out`, from its `Shape`. -/
theorem outOk_of_shape {P : Impl.MdStream.X86.Params} {H : Md P.B P.N P.L} (hs : Proof.MdStream.X86.Shape H) :
    OutOk H P.out := fun s hbx hax hin hout hd =>
  WP.mono (hs.out s hbx hax hin hout hd) fun _ ⟨g, rd, wr, m⟩ => ⟨fun r h _ => g r h, rd, wr, m⟩

def md5Ok : MdOk md5M where
  hH := md5OK
  md := Proof.Md5.md
  iv := Spec.Md5.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm, by decide, by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  tail := by decide
  out := outOk_of_shape Proof.Md5.X86.Stream.shape
  comp := ⟨Proof.Md5.X86.compress_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
  sizes := ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

def sha1Ok : MdOk sha1M where
  hH := sha1OK
  md := Proof.Sha1.md
  iv := Spec.Sha1.H0
  link := ⟨rfl, rfl, rfl, fun _ _ _ h => h, fun m => by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm, by decide, by decide⟩
  back _ _ _ h := h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
  tail := by decide
  out := outOk_of_shape Proof.Sha1.X86.Stream.shape
  comp := ⟨Proof.Sha1.X86.compress_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
  sizes := ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

/-- `MdOk` for a member of the SHA-512 family, whose digest is the first `D`
bytes of the final hash value. -/
def sha512Ok {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}
    (hO : VG.Proof.Pbkdf2.Stream.X86.HashOK (sha512H D initN iv)) (hR : hO.SH.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, hO.SH.H.hash m = (Spec.Sha512.finalHash iv m).take D) (hB : hO.SH.H.blockSize = 128)
    (hS : hO.SH.stateBytes = 192) (hD : hO.SH.digestBytes = D) (hD64 : D ≤ 64)
    (tail : Proof.Sha512.md.tailPad D = (sha512M D initN iv).tailB) (sizes : Sizes (sha512M D initN iv)) :
    MdOk (sha512M D initN iv) where
  hH := hO
  md := Proof.Sha512.md
  iv := iv
  link := ⟨hB, hS, hD, fun _ _ _ h => by rw [hR] at h; exact h, hh, hD64, by have := sizes.DL; omega⟩
  back _ _ _ h := by rw [hR]; exact h
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  tail := tail
  out := outOk_of_shape Proof.Sha512.X86.Stream.shape
  comp := ⟨Proof.Sha512.X86.Compress.compress_verified, NoSp.of_all (by lit_decide), by lit_decide⟩
  sizes := sizes

def sha384Ok : MdOk sha384M := sha512Ok sha384OK rfl (fun _ => rfl) rfl rfl rfl (by decide) (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512Ok' : MdOk sha512M' := sha512Ok sha512OK rfl
  (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm)
  rfl rfl rfl (by decide) (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512_224Ok : MdOk sha512_224M := sha512Ok sha512_224OK rfl (fun _ => rfl) rfl rfl rfl (by decide)
  (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩
def sha512_256Ok : MdOk sha512_256M := sha512Ok sha512_256OK rfl (fun _ => rfl) rfl rfl rfl (by decide)
  (by decide) ⟨by decide, by decide, by decide, by decide, rfl, by decide, by decide, by decide⟩

end VG.Proof.Pbkdf2.Md.X86
