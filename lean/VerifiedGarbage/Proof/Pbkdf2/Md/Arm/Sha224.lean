import VerifiedGarbage.Proof.Pbkdf2.Md.Arm.Sha256
import VerifiedGarbage.Proof.Pbkdf2.Stream.Arm.Sha224

/-!
# HMAC-SHA-224 and PBKDF2-HMAC-SHA-224 over the compression function on ARMv7

SHA-224 as a `Hash`: its streaming functions as the code calls them
(`sha224H`, `Proof/Pbkdf2/Stream/Arm/Sha224.lean`), SHA-256's hash value,
length field, digest code and compression function (`Sha256.lean`); what the
proofs need of it (`HashOK`), with SHA-256's `Md` from SHA-224's initial hash
value and the digest its first 28 bytes; and the generic proofs at it, moved
to the shared contracts of `Spec.Hmac.sha224I` (as for the hash functions of
`Instances.lean`).
-/

namespace VG.Proof.Pbkdf2.Md.Arm

open VG VG.Arm VG.Proof.MdStream
open VG.Impl.Pbkdf2.Md.Arm (Hash)
open VG.Proof.Pbkdf2.Stream.Arm (sha224H sha224OK)

/-- SHA-224: SHA-256's 32-byte hash value, big-endian length field and
`vg_sha256_compress`, with 112 bytes of scratch space. -/
def sha224Md : Hash where
  st := sha224H
  N := 32
  L := 8
  be := true
  so := 112
  out := Impl.Sha256.Arm.Stream.params.out
  compN := "vg_sha256_compress"
  compC := Impl.Sha256.Arm.compress

def sha224MdOK : HashOK sha224Md where
  md := Proof.Sha256.md
  out := OutOk.ofShape Proof.Sha256.Arm.Stream.shape
  comp := sha256_comp
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  len := by decide
  stream := sha224OK
  iv := Spec.Sha256.H0_224
  repr _ _ _ h := h
  back _ _ _ h := h
  hash _ := rfl
  sizes := ⟨.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

end VG.Proof.Pbkdf2.Md.Arm

namespace VG.Proof.Pbkdf2.Md.Arm.Instances

open VG.Arm
open VG.Proof.Pbkdf2.Md.Arm
open VG.Proof.Pbkdf2.Stream.Arm (initG finG iterG below count)

theorem sha224_iterChecks : Iterate.Checks sha224Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha224_finChecks : Fin.Checks sha224Md :=
  ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩

theorem sha224_iterImp : (iterG Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.iterateContract Arm.abi 16) :=
  iterImp Spec.Hmac.sha224S 104 (by
    inst_sat [Spec.Pbkdf2.iterateContract, Spec.Pbkdf2.iterateSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, iterG,
      below, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using iterSat 96 28 104)

theorem sha224_iterate : Verified Arm.target sha224Md.iterate (Spec.Hmac.sha224I.iterateContract Arm.abi 16) :=
  (Iterate.verified sha224MdOK sha224_iterChecks (by decide) sha224_iterImp.sat_left).of_implies sha224_iterImp

theorem sha224_initChecks : HmacInit.Checks sha224Md :=
  ⟨⟨_, by taint_decide⟩, by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩

theorem sha224_initImp : (initG Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.initContract Arm.abi 16) :=
  initImp Spec.Hmac.sha224S 104 (by
    inst_sat [Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 96 104)

theorem sha224_finImp : (finG Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha224S 104 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 96 28 104)

theorem sha224_init : Verified Arm.target sha224Md.hmacInit (Spec.Hmac.sha224I.initContract Arm.abi 16) :=
  (HmacInit.verified sha224MdOK sha224_initChecks (by decide) sha224_initImp.sat_left).of_implies sha224_initImp

theorem sha224_finalize : Verified Arm.target sha224Md.hmacFin (Spec.Hmac.sha224I.finalizeContract Arm.abi 16) :=
  (Fin.verified sha224MdOK sha224_finChecks (by decide) sha224_finImp.sat_left).of_implies
    sha224_finImp

end VG.Proof.Pbkdf2.Md.Arm.Instances
