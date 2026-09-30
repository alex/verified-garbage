import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Sha1.AArch64.Shared
import VerifiedGarbage.Proof.Sha1.Md
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.TCB.AArch64.Target

/-!
# SHA-1 on AArch64, as a Merkle–Damgård hash function

Untrusted: everything here is checked by Lean. SHA-1 with its compression
function, as a variant of `MdHash` (`variant`), from which HMAC and PBKDF2
are emitted (`Generic/MdHash/AArch64/`): its streaming code is the generic
Merkle–Damgård code (`Stream.params`), its specification `Spec.Hmac.sha1S`.
The facts about the code HMAC and PBKDF2 add, which do not depend on the
functions they call, are checked once (`coreOK`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha1

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64.Instances (initSat finSat)

/-- SHA-1's functions. -/
def hash : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha1.AArch64.Stream.params
  D := 20
  W := Spec.Hmac.sha1I.scratch
  compN := Spec.Sha1.compressApi.name
  compC := Impl.Sha1.AArch64.compress
  initN := Spec.Sha1.initApi.name
  initC := Impl.Sha1.AArch64.Stream.init
  updN := Spec.Sha1.updateApi.name
  updC := Impl.Sha1.AArch64.Stream.update
  finN := Spec.Sha1.finalizeApi.name
  finC := Impl.Sha1.AArch64.Stream.finalize
  hmacInitN := Spec.Hmac.sha1I.initApi.name
  hmacFinN := Spec.Hmac.sha1I.finalizeApi.name
  iterN := Spec.Hmac.sha1I.iterateApi.name

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha1.AArch64.Stream.params, 20, 56, "", .block [], "",
  .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK : CoreOK coreH where
  pbk := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  iter := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  hinit := {
    keys := ⟨_, by taint_decide⟩
    argI := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
    argU₁ := ⟨_, by taint_decide⟩
    argU₂ := ⟨_, by taint_decide⟩
    restore := ⟨_, by taint_decide⟩ }
  hfin := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩⟩
  fitI := by decide
  fitF := by decide

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Hmac.Generic.AArch64.HashOK hash.stream where
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
  repr := Hmac.Generic.Common.sha1_repr
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

def ok : HashOK hash where
  md := Proof.Sha1.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha1.AArch64.Stream.shape
  comp := ⟨Proof.Sha1.AArch64.Stream.callee.verified, Proof.Sha1.AArch64.compress_verified.2.1,
    Proof.Sha1.AArch64.Stream.callee.noFrames⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha1.md, Spec.Sha1.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 20) h (by omega)
  lenOk _ _ := trivial
  stream := streamOK
  iv := Spec.Sha1.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha1.hash m = _
    rw [Proof.Sha1.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha1.md.digest_length _))).symm
  sizes := ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  L := by decide
  W := by decide

theorem satI : ∃ s, (Spec.Hmac.sha1I.initContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha1I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using initSat 84 56

theorem satF : ∃ s, (Spec.Hmac.sha1I.finalizeContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha1I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs] using finSat 84 20 56

theorem satT : ∃ s, (Spec.Hmac.sha1I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha1I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 84 20 56

theorem satP : ∃ s, (Spec.Hmac.sha1I.pbkdf2Contract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha1I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha1S, Spec.Hmac.sha1, AArch64.abi,
    AArch64.argRegs] using pbkSat 140

/-- SHA-1 with its compression function. -/
def variant : MdHash := MdHash.of ok coreOK rfl rfl satI satF satT satP "" []

end VG.Proof.Pbkdf2.Md.AArch64.Sha1
