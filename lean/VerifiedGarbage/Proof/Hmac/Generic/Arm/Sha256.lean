import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances
import VerifiedGarbage.Proof.Sha256.Arm.Shared

/-!
# HMAC-SHA-256 on 32-bit ARM

`HashOK` for SHA-256 (`sha256OK`): its streaming functions
(`vg_sha256_init`, `vg_sha256_update` and `vg_sha256_finalize`, whose
contracts for `update` and `finalize` hold from any initial hash value); and
the generic HMAC proofs at it, moved to the shared contracts of
`Spec.Hmac.sha256I` (as for the hash functions of `Hashes.lean` in
`Instances.lean`).
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash)

/-- SHA-256's functions: a 96-byte streaming state, 20 words of working
space and a 32-byte digest. -/
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
  repr := Common.sha256_repr
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

end VG.Proof.Hmac.Generic.Arm

namespace VG.Proof.Hmac.Generic.Arm.Instances

open VG.Arm
open VG.Proof.Hmac.Generic.Arm

theorem sha256_initChecks : Init.Checks sha256H where
  keys := ⟨_, by taint_decide⟩
  argI := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
  argU₁ := ⟨_, by taint_decide⟩
  argU₂ := ⟨_, by taint_decide⟩
  restore := ⟨_, by taint_decide⟩

theorem sha256_initImp : (initG Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.initContract Arm.abi 16) :=
  initImp Spec.Hmac.sha256S 104 (by
    inst_sat [Spec.Hmac.initContract, Spec.Hmac.initSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, initG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 96 104)

theorem sha256_finImp : (finG Spec.Hmac.sha256S 104).Implies (Spec.Hmac.sha256I.finalizeContract Arm.abi 16) :=
  finImp Spec.Hmac.sha256S 104 (by
    inst_sat [Spec.Hmac.finalizeContract, Spec.Hmac.finalizeSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, finG,
      below, count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using finSat 96 32 104)

theorem sha256_init : Verified Arm.target sha256H.init (Spec.Hmac.sha256I.initContract Arm.abi 16) :=
  (Init.verified sha256OK sha256_initChecks (by decide) sha256_initImp.sat_left).of_implies sha256_initImp

end VG.Proof.Hmac.Generic.Arm.Instances
