import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.IterateCT
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.HmacFinCT
import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha512
import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances
import VerifiedGarbage.Proof.Sha1.Arm.Stream.Md
import VerifiedGarbage.Proof.Md5.Arm.Stream.Md
import VerifiedGarbage.Proof.Sha1.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Lit
import VerifiedGarbage.Proof.Sha512.Arm.Shared

/-!
# HMAC and PBKDF2-HMAC over Merkle–Damgård hash functions on ARMv7: the instances

MD5, SHA-1 and the SHA-512 family as `Hash`es (their streaming functions as
HMAC's `init` calls them, `Proof/Hmac/Generic/Arm/Hashes.lean`, with their
hash value, length field, digest code and compression function), what the
proofs need of them (`HashOK`, from the hash functions' own proofs), and the
generic proofs of HMAC's `finalize` and PBKDF2's iteration (`HmacFinCT.lean`,
`IterateCT.lean`) at each of them, moved to the shared contracts of
`Spec/Hmac/Generic.lean` and `Spec/Pbkdf2/Generic.lean`, which the artifacts
are emitted with. SHA-256 and SHA-224 are in `Sha256.lean` and
`Sha224.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Hmac.Generic.Arm (iterG below sha1H md5H sha384H sha512H' sha512_224H sha512_256H sha1OK md5OK
  sha384OK sha512OK sha512_224OK sha512_256OK)

/-! ## The hash functions -/

/-- SHA-1: a 20-byte hash value, a big-endian length field, and
`vg_sha1_compress`, with 112 bytes of scratch space. -/
def sha1Md : Hash where
  st := sha1H
  N := 20
  L := 8
  be := true
  so := 112
  out := Impl.Sha1.Arm.Stream.params.out
  compN := "vg_sha1_compress"
  compC := Impl.Sha1.Arm.compress

/-- MD5: a 16-byte hash value, a little-endian length field, and
`vg_md5_compress`, with 64 bytes of scratch space. -/
def md5Md : Hash where
  st := md5H
  N := 16
  L := 8
  be := false
  so := 64
  out := Impl.Md5.Arm.Stream.params.out
  compN := "vg_md5_compress"
  compC := Impl.Md5.Arm.compress

/-- The member of the SHA-512 family with a `D`-byte digest, initial hash
value `iv` and streaming `init` named `initN`: a 64-byte hash value, a
16-byte big-endian length field, and `vg_sha512_compress`, with 224 bytes of
scratch space. -/
def sha512Md (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  st := Hmac.Generic.Arm.sha512H D initN iv
  N := 64
  L := 16
  be := true
  so := 224
  out := (List.range 8).flatMap Impl.Sha512.Arm.Stream.outW
  compN := "vg_sha512_compress"
  compC := Impl.Sha512.Arm.compress

def sha384Md : Hash := sha512Md 48 "vg_sha384_init" Spec.Sha512.H0_384
def sha512Md' : Hash := sha512Md 64 "vg_sha512_init" Spec.Sha512.H0_512
def sha512_224Md : Hash := sha512Md 28 "vg_sha512_224_init" Spec.Sha512.H0_512_224
def sha512_256Md : Hash := sha512Md 32 "vg_sha512_256_init" Spec.Sha512.H0_512_256

/-! ## What the proofs need of them -/

theorem sha1_comp : CompOk Proof.Sha1.md 112 Impl.Sha1.Arm.compress :=
  ⟨Proof.Sha1.Arm.compress_verified.1, Proof.Sha1.Arm.compress_verified.2.1, by lit_decide,
    by rw [← Code.allInstrs_eq]; lit_decide⟩

def sha1MdOK : HashOK sha1Md where
  md := Proof.Sha1.md
  out := OutOk.ofShape Proof.Sha1.Arm.Stream.shape
  comp := sha1_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
  len := by decide
  stream := sha1OK
  iv := Spec.Sha1.H0
  repr _ _ _ h := h
  hash m := by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm
  sizes := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem md5_comp : CompOk Proof.Md5.md 64 Impl.Md5.Arm.compress :=
  ⟨Proof.Md5.Arm.compress_verified.1, Proof.Md5.Arm.compress_verified.2.1, by decide +kernel,
    by rw [← Code.allInstrs_eq]; decide +kernel⟩

def md5MdOK : HashOK md5Md where
  md := Proof.Md5.md
  out := OutOk.ofShape Proof.Md5.Arm.Stream.shape
  comp := md5_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  len := by decide
  stream := md5OK
  iv := Spec.Md5.H0
  repr _ _ _ h := h
  hash m := by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm
  sizes := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

theorem sha512_comp : CompOk Proof.Sha512.md 224 Impl.Sha512.Arm.compress :=
  ⟨Proof.Sha512.Arm.Compress.compress_verified.1, Proof.Sha512.Arm.Compress.compress_verified.2.1, by lit_decide,
    by rw [← Code.allInstrs_eq]; lit_decide⟩

/-- `HashOK` for the member of the SHA-512 family with a `D`-byte digest, from
the initial hash value `iv`. -/
def sha512MdOK {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}
    (hs : Hmac.Generic.Arm.HashOK (Hmac.Generic.Arm.sha512H D initN iv))
    (hR : hs.SH.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, hs.SH.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hz : Sizes (sha512Md D initN iv))
    (hlen : wordsBytes (Impl.Pbkdf2.Md.Arm.lenWords true 16 (128 + D)) = Proof.Sha512.md.lenBytes (128 + D)) :
    HashOK (sha512Md D initN iv) where
  md := Proof.Sha512.md
  out := sha512_out
  comp := sha512_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  len := hlen
  stream := hs
  iv := iv
  repr mem p m h := by rw [hR] at h; exact Proof.Sha512.repr_iff.mp h
  hash m := by rw [hh, Proof.Sha512.finalHash_eq]; rfl
  sizes := hz

def sha384MdOK : HashOK sha384Md :=
  sha512MdOK sha384OK rfl (fun _ => rfl)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

def sha512MdOK' : HashOK sha512Md' :=
  sha512MdOK sha512OK rfl
    (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

def sha512_224MdOK : HashOK sha512_224Md :=
  sha512MdOK sha512_224OK rfl (fun _ => rfl)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

def sha512_256MdOK : HashOK sha512_256Md :=
  sha512MdOK sha512_256OK rfl (fun _ => rfl)
    ⟨.inr rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide⟩ (by decide)

end VG.Proof.Pbkdf2.Md.Arm

namespace VG.Proof.Pbkdf2.Md.Arm.Instances

open VG.Arm
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Hmac.Generic.Arm (iterG below)

/-- A state satisfying `iterate`'s precondition, with states of `S` bytes, a
digest of `D` bytes and `8 sc` bytes of scratch space; `scratch`, at
`0x4000`, is the stack argument. -/
def iterSat (S D sc : Nat) : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | .r3 => 0x3000
    | _ => 0
  sp := 0x6000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x6001 then 0x40 else 0
  rd := [⟨0x1000, 2 * S⟩, ⟨0x2000, D⟩, ⟨0x6000, 4⟩]
  wr := [⟨0x3000, D⟩, ⟨0x4000, 8 * sc⟩]

/-- `iterG` implies the shared contract for any hash function and scratch space
(`generic_implies`), given that the shared contract is satisfiable. -/
theorem iterImp (S : Spec.Hmac.StreamingHash) (W : Nat) (h : ∃ s, (Spec.Pbkdf2.iterateContract S W Arm.abi 16).pre s) :
    (iterG S W).Implies (Spec.Pbkdf2.iterateContract S W Arm.abi 16) := by
  generic_implies [
    Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, iterG, below, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using h

/-! ## SHA-1 -/

theorem sha1_iterChecks : Iterate.Checks sha1Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha1_finChecks : Fin.Checks sha1Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha1_iterImp : (iterG Spec.Hmac.sha1S 56).Implies (Spec.Hmac.sha1I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha1S 56 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 84 20 56)

theorem sha1_iterate : Verified Arm.target sha1Md.iterate (Spec.Hmac.sha1I.iterateContract Arm.abi 16) :=
  (Iterate.verified sha1MdOK sha1_iterChecks (by decide) sha1_iterImp.sat_left).of_implies sha1_iterImp

theorem sha1_finalize : Verified Arm.target sha1Md.hmacFin (Spec.Hmac.sha1I.finalizeContract Arm.abi 16) :=
  (Fin.verified sha1MdOK sha1_finChecks (by decide) Hmac.Generic.Arm.Instances.sha1_finImp.sat_left).of_implies
    Hmac.Generic.Arm.Instances.sha1_finImp

/-! ## MD5 -/

theorem md5_iterChecks : Iterate.Checks md5Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem md5_finChecks : Fin.Checks md5Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem md5_iterImp : (iterG Spec.Hmac.md5S 48).Implies (Spec.Hmac.md5I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.md5S 48 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 80 16 48)

theorem md5_iterate : Verified Arm.target md5Md.iterate (Spec.Hmac.md5I.iterateContract Arm.abi 16) :=
  (Iterate.verified md5MdOK md5_iterChecks (by decide) md5_iterImp.sat_left).of_implies md5_iterImp

theorem md5_finalize : Verified Arm.target md5Md.hmacFin (Spec.Hmac.md5I.finalizeContract Arm.abi 16) :=
  (Fin.verified md5MdOK md5_finChecks (by decide) Hmac.Generic.Arm.Instances.md5_finImp.sat_left).of_implies
    Hmac.Generic.Arm.Instances.md5_finImp

/-! ## SHA-384 -/

theorem sha384_iterChecks : Iterate.Checks sha384Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha384_finChecks : Fin.Checks sha384Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha384_iterImp : (iterG Spec.Hmac.sha384S 234).Implies (Spec.Hmac.sha384I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha384S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 48 234)

theorem sha384_iterate : Verified Arm.target sha384Md.iterate (Spec.Hmac.sha384I.iterateContract Arm.abi 16) :=
  (Iterate.verified sha384MdOK sha384_iterChecks (by decide) sha384_iterImp.sat_left).of_implies sha384_iterImp

theorem sha384_finalize : Verified Arm.target sha384Md.hmacFin (Spec.Hmac.sha384I.finalizeContract Arm.abi 16) :=
  (Fin.verified sha384MdOK sha384_finChecks (by decide) Hmac.Generic.Arm.Instances.sha384_finImp.sat_left).of_implies
    Hmac.Generic.Arm.Instances.sha384_finImp

/-! ## SHA-512 -/

theorem sha512_iterChecks : Iterate.Checks sha512Md' :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_finChecks : Fin.Checks sha512Md' :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_iterImp : (iterG Spec.Hmac.sha512S 234).Implies (Spec.Hmac.sha512I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha512S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 64 234)

theorem sha512_iterate : Verified Arm.target sha512Md'.iterate (Spec.Hmac.sha512I.iterateContract Arm.abi 16) :=
  (Iterate.verified sha512MdOK' sha512_iterChecks (by decide) sha512_iterImp.sat_left).of_implies sha512_iterImp

theorem sha512_finalize : Verified Arm.target sha512Md'.hmacFin (Spec.Hmac.sha512I.finalizeContract Arm.abi 16) :=
  (Fin.verified sha512MdOK' sha512_finChecks (by decide) Hmac.Generic.Arm.Instances.sha512_finImp.sat_left).of_implies
    Hmac.Generic.Arm.Instances.sha512_finImp

/-! ## SHA-512/224 -/

theorem sha512_224_iterChecks : Iterate.Checks sha512_224Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_224_finChecks : Fin.Checks sha512_224Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_224_iterImp : (iterG Spec.Hmac.sha512_224S 234).Implies (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha512_224S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 28 234)

theorem sha512_224_iterate : Verified Arm.target sha512_224Md.iterate (Spec.Hmac.sha512_224I.iterateContract Arm.abi 16) :=
  (Iterate.verified sha512_224MdOK sha512_224_iterChecks (by decide) sha512_224_iterImp.sat_left).of_implies sha512_224_iterImp

theorem sha512_224_finalize : Verified Arm.target sha512_224Md.hmacFin (Spec.Hmac.sha512_224I.finalizeContract Arm.abi 16) :=
  (Fin.verified sha512_224MdOK sha512_224_finChecks (by decide) Hmac.Generic.Arm.Instances.sha512_224_finImp.sat_left).of_implies
    Hmac.Generic.Arm.Instances.sha512_224_finImp

/-! ## SHA-512/256 -/

theorem sha512_256_iterChecks : Iterate.Checks sha512_256Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_256_finChecks : Fin.Checks sha512_256Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha512_256_iterImp : (iterG Spec.Hmac.sha512_256S 234).Implies (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha512_256S 234 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, iterG, below,
      Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 192 32 234)

theorem sha512_256_iterate : Verified Arm.target sha512_256Md.iterate (Spec.Hmac.sha512_256I.iterateContract Arm.abi 16) :=
  (Iterate.verified sha512_256MdOK sha512_256_iterChecks (by decide) sha512_256_iterImp.sat_left).of_implies sha512_256_iterImp

theorem sha512_256_finalize : Verified Arm.target sha512_256Md.hmacFin (Spec.Hmac.sha512_256I.finalizeContract Arm.abi 16) :=
  (Fin.verified sha512_256MdOK sha512_256_finChecks (by decide) Hmac.Generic.Arm.Instances.sha512_256_finImp.sat_left).of_implies
    Hmac.Generic.Arm.Instances.sha512_256_finImp

end VG.Proof.Pbkdf2.Md.Arm.Instances
