import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Md5.AArch64.Shared
import VerifiedGarbage.Proof.Md5.Md
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.TCB.AArch64.Target

/-!
# MD5 on AArch64, as a Merkle–Damgård hash function

Untrusted: everything here is checked by Lean. MD5 with its compression
function, as a variant of `MdHash` (`variant`), from which HMAC and PBKDF2
are emitted (`Generic/MdHash/AArch64/`): its streaming code is the generic
Merkle–Damgård code (`Stream.params`), its specification `Spec.Hmac.md5S`.
The facts about the code HMAC and PBKDF2 add, which do not depend on the
functions they call, are checked once (`coreOK`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Md5

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64.Instances (initSat finSat)

/-- MD5's functions. -/
def hash : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Md5.AArch64.Stream.params
  D := 16
  W := Spec.Hmac.md5I.scratch
  compN := Spec.Md5.compressApi.name
  compC := Impl.Md5.AArch64.compress
  initN := Spec.Md5.initApi.name
  initC := Impl.Md5.AArch64.Stream.init
  updN := Spec.Md5.updateApi.name
  updC := Impl.Md5.AArch64.Stream.update
  finN := Spec.Md5.finalizeApi.name
  finC := Impl.Md5.AArch64.Stream.finalize
  hmacInitN := Spec.Hmac.md5I.initApi.name
  hmacFinN := Spec.Hmac.md5I.finalizeApi.name
  iterN := Spec.Hmac.md5I.iterateApi.name

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Md5.AArch64.Stream.params, 16, 48, "", .block [], "",
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
  repr := Hmac.Generic.Common.md5_repr
  init := Proof.Md5.AArch64.Stream.init_verified
  upd := Proof.Md5.AArch64.Stream.Update.update_verified
  fin := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 16 (Spec.Md5.bytesAt s'.mem _ 16) = _
        rw [List.take_of_length_le (by simp [Spec.Md5.bytesAt])]
        exact h m hr hc
      pub := fun _ _ _ _ h => h
      sat := Proof.Md5.AArch64.Stream.Finalize.finalize_verified.2.2 }
  initDepth := by decide +kernel
  updDepth := by decide +kernel
  finDepth := by decide +kernel

def ok : HashOK hash where
  md := Proof.Md5.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Md5.AArch64.Stream.shape
  comp := ⟨Proof.Md5.AArch64.Stream.callee.verified, Proof.Md5.AArch64.compress_verified.2.1,
    Proof.Md5.AArch64.Stream.callee.noFrames⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Md5.md, Spec.Md5.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 16) h (by omega)
  lenOk _ _ := trivial
  stream := streamOK
  iv := Spec.Md5.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Md5.hash m = _
    rw [Proof.Md5.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Md5.md.digest_length _))).symm
  sizes := ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩
  L := by decide
  W := by decide

theorem satI : ∃ s, (Spec.Hmac.md5I.initContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.md5I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using initSat 80 48

theorem satF : ∃ s, (Spec.Hmac.md5I.finalizeContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.md5I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs] using finSat 80 16 48

theorem satT : ∃ s, (Spec.Hmac.md5I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.md5I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 80 16 48

theorem satP : ∃ s, (Spec.Hmac.md5I.pbkdf2Contract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.md5I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.md5S, Spec.Hmac.md5, AArch64.abi,
    AArch64.argRegs] using pbkSat 128

/-- MD5 with its compression function. -/
def variant : MdHash := MdHash.of ok coreOK rfl rfl satI satF satT satP "" []

end VG.Proof.Pbkdf2.Md.AArch64.Md5
