import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/-!
# HMAC-SHA-224 on 32-bit ARM

`HashOK` for SHA-224 (`sha224OK`): SHA-256's streaming functions from
SHA-224's initial hash value (`vg_sha224_init`, then `vg_sha256_update` and
`vg_sha256_finalize`, whose contracts hold from any initial hash value), with
the digest the first 28 bytes of the final hash value; and the generic HMAC
proofs at it, moved to the shared contracts of `Spec.Hmac.sha224I` (as for the
hash functions of `Hashes.lean` in `Instances.lean`).
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)
open VG.Proof.Hmac.Generic.Common (readW_reloc bytesAt_reloc)

/-- SHA-224's functions: SHA-256's streaming state, 96 bytes, and working
space, 20 words; a 28-byte digest, of the 32 bytes `finalize` writes. -/
def sha224H : Hash := ⟨64, 96, 28, 32, 20, "vg_sha224_init", Impl.Sha256.Arm.Stream.init224,
  "vg_sha256_update", Impl.Sha256.Arm.Stream.update, "vg_sha256_finalize", Impl.Sha256.Arm.Stream.finalize⟩

/-- The representation moves with the state's bytes. -/
theorem sha224_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m p msg) :
    Spec.Sha256.ReprFrom Spec.Sha256.H0_224 m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact readW_reloc h (by omega)
  · rw [← hr.2]
    exact bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega)

def sha224OK : HashOK sha224H where
  SH := Spec.Hmac.sha224S
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
  repr := sha224_repr
  init := Proof.Sha256.Arm.Stream.init224_verified
  upd := Proof.Sha256.Arm.Stream.Update.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0_224 m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Update.update_verified.2.2 }
  fin := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 28 (Spec.Sha256.bytesAt s'.mem _ 32) = Spec.Sha256.sha224 m
        rw [h Spec.Sha256.H0_224 m hr hc]
        rfl
      pub := fun _ _ _ _ h => h
      sat := Proof.Sha256.Arm.Stream.Finalize.finalize_verified.2.2 }
  initNF := by decide +kernel
  updNF := by decide +kernel
  finNF := by decide +kernel

end VG.Proof.Hmac.Generic.Arm

namespace VG.Proof.Hmac.Generic.Arm.Instances

open VG.Arm
open VG.Proof.Hmac.Generic.Arm

theorem sha224_initChecks : Init.Checks sha224H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha224_initImp : (initG Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.initContract Arm.abi 16) :=
  initImp Spec.Hmac.sha224S 104 (by
    inst_sat [Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 96 104)

theorem sha224_finImp : (finG Spec.Hmac.sha224S 104).Implies (Spec.Hmac.sha224I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha224S 104 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha224S, Spec.Hmac.sha224, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 96 28 104)

theorem sha224_init : Verified Arm.target sha224H.init (Spec.Hmac.sha224I.initContract Arm.abi 16) :=
  (Init.verified sha224OK sha224_initChecks (by decide) sha224_initImp.sat_left).of_implies sha224_initImp

end VG.Proof.Hmac.Generic.Arm.Instances
