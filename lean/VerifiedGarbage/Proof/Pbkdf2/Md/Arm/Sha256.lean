import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Instances
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha256
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
import VerifiedGarbage.Proof.Sha256.Arm.Lit

/-!
# HMAC-SHA-256 and PBKDF2-HMAC-SHA-256 over the compression function on ARMv7

SHA-256 as a `Hash`: its streaming functions as the code calls them
(`sha256H`, `Proof/Pbkdf2/Stream/Arm/Sha256.lean`), its hash value, length
field, digest code and compression function (`vg_sha256_compress`, which
SHA-224 shares: `Sha224.lean`); what the proofs need of it (`HashOK`), with
SHA-256's `Md` from `H0`; and the generic proofs at it, moved to the shared
contracts of `Spec.Hmac.sha256I` (as for the hash functions of
`Instances.lean`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (sha256H sha256OK)

/-- SHA-256: a 32-byte hash value, a big-endian length field and
`vg_sha256_compress`, with 112 bytes of scratch space. -/
def sha256Md : Hash where
  st := sha256H
  N := 32
  L := 8
  be := true
  so := 112
  out := Impl.Sha256.Arm.Stream.params.out
  compN := "vg_sha256_compress"
  compC := Impl.Sha256.Arm.compress

theorem sha256_comp : CompOk Proof.Sha256.md 112 Impl.Sha256.Arm.compress :=
  ⟨Proof.Sha256.Arm.compress_verified.1, Proof.Sha256.Arm.compress_verified.2.1, by lit_decide,
    by rw [← Code.allInstrs_eq]; lit_decide⟩

def sha256MdOK : HashOK sha256Md where
  md := Proof.Sha256.md
  out := OutOk.ofShape Proof.Sha256.Arm.Stream.shape
  comp := sha256_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  len := by decide
  stream := sha256OK
  iv := Spec.Sha256.H0
  repr _ _ _ h := h
  back _ _ _ h := h
  hash m := by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm
  sizes := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

end VG.Proof.Pbkdf2.Md.Arm

namespace VG.Proof.Pbkdf2.Md.Arm.Instances

open VG.Arm
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Pbkdf2.Stream.Arm (initG finG iterG below count)

theorem sha256_iterChecks : Iterate.Checks sha256Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha256_finChecks : Fin.Checks sha256Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha256_iterImp : (iterG Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha256S 104 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, iterG,
      below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 96 32 104)

theorem sha256_iterate : Verified Arm.target sha256Md.iterate (Spec.Hmac.sha256I.iterateContract Arm.abi 16) :=
  (Iterate.verified sha256MdOK sha256_iterChecks (by decide) sha256_iterImp.sat_left).of_implies sha256_iterImp

theorem sha256_initChecks : HmacInit.Checks sha256Md :=
  ⟨⟨_, by taint_decide⟩, by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩

theorem sha256_initImp : (initG Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.initContract Arm.abi 16) :=
  initImp Spec.Hmac.sha256S 104 (by
    inst_sat [Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 96 104)

theorem sha256_finImp : (finG Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha256S 104 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 96 32 104)

theorem sha256_init : Verified Arm.target sha256Md.hmacInit (Spec.Hmac.sha256I.initContract Arm.abi 16) :=
  (HmacInit.verified sha256MdOK sha256_initChecks (by decide) sha256_initImp.sat_left).of_implies sha256_initImp

theorem sha256_finalize : Verified Arm.target sha256Md.hmacFin (Spec.Hmac.sha256I.finalizeContract Arm.abi 16) :=
  (Fin.verified sha256MdOK sha256_finChecks (by decide) sha256_finImp.sat_left).of_implies
    sha256_finImp

end VG.Proof.Pbkdf2.Md.Arm.Instances
