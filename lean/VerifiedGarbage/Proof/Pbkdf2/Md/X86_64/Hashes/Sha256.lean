import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Sha256.X86_64.Variant
import VerifiedGarbage.Proof.Sha256.X86_64.Shared
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.TCB.X86_64.Target

/-!
# SHA-256 on x86-64, as a Merkle–Damgård hash function

SHA-256 with an implementation `v` of its compression function
(`Proof/Sha256/X86_64/Variant.lean`), as a variant of `MdHash` (`variant v`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/X86_64/`): its streaming
code is the generic Merkle–Damgård code (`Stream.params`), its specification
`Spec.Hmac.sha256S`. The facts about the code HMAC and PBKDF2 add, which do not
depend on `v`, are checked once (`coreOK`).

`stream v` are the streaming `update` and `finalize` made with `v`, which
`Generic/MdHash/X86_64/Stream.lean` emits from their `Api`s, named with
its suffix.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha256

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha256.X86_64 (Compress)
open VG.Proof.Hmac.Generic.X86_64.Instances (initSat finSat)

/-- SHA-256's functions, calling the implementation `v` of the compression
function, named with its suffix. -/
def hash (v : Compress) : Hash where
  P := Impl.Sha256.X86_64.Stream.params
  D := 32
  W := Spec.Hmac.sha256I.scratch
  compN := v.callee.name
  compC := v.callee.code
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.X86_64.Stream.init
  updN := Spec.Sha256.updateApi.name ++ v.suffix
  finN := Spec.Sha256.finalizeApi.name ++ v.suffix
  hmacInitN := Spec.Hmac.sha256I.initApi.name ++ v.suffix
  hmacFinN := Spec.Hmac.sha256I.finalizeApi.name ++ v.suffix
  iterN := Spec.Hmac.sha256I.iterateApi.name ++ v.suffix

/-- `hash v` without the functions it calls, the same for every `v`. -/
def coreH : Hash := ⟨Impl.Sha256.X86_64.Stream.params, 32, 104, "", .block [], "", .block [], "", "", "", "",
  ""⟩

theorem coreOK : CoreOK coreH where
  pbk := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  iter := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
    ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  hinit := {
    keys := ⟨_, by taint_decide⟩
    argI := by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro st (rfl | rfl) <;> exact ⟨_, by taint_decide⟩
    argU₁ := ⟨_, by taint_decide⟩
    argU₂ := ⟨_, by taint_decide⟩
    restore := ⟨_, by taint_decide⟩ }
  hfin := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  pbkMx := by decide +kernel
  pbkSp := by decide +kernel
  hinitMx := by decide +kernel
  hinitSp := by decide +kernel
  hinitNs := by decide +kernel
  hinitD := by decide +kernel
  hfinMx := by decide +kernel
  hfinSp := by decide +kernel
  hfinNs := by decide +kernel
  hfinD := by decide +kernel
  iterMx := by decide +kernel
  iterSp := by decide +kernel
  iterNs := by decide +kernel
  iterD := by decide +kernel
  updMx := by decide +kernel
  updNs := by decide +kernel
  updD := by decide +kernel
  finMx := by decide +kernel
  finNs := by decide +kernel
  finD := by decide +kernel
  fitI := by decide
  fitF := by decide

variable (v : Compress)

theorem callees : Callees (hash v) where
  cMx := v.mxcsr
  cSp := allInstrs_of_all v.spSafe
  cNs := by
    show v.callee.code.allInstrs _ = true
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]
  cD := v.ok.depth
  iMx := by simp only [hash] <;> decide +kernel
  iSp := by simp only [hash] <;> decide +kernel
  iNs := by simp only [hash] <;> decide +kernel
  iD := by simp only [hash] <;> decide +kernel

def ok : HashOK (hash v) where
  md := Proof.Sha256.md
  dims := Proof.Sha256.X86_64.Stream.dims
  shape := Proof.Sha256.X86_64.Stream.shape
  taints := Proof.Sha256.X86_64.Stream.taints
  comp := Proof.Sha256.X86_64.Stream.callee v.ok
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  lenOk _ _ := trivial
  SH := Spec.Hmac.sha256S
  iv := Spec.Sha256.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm
  hB := rfl
  hS := rfl
  hD := rfl
  hD0 := by simp only [hash] <;> decide
  hDN := by simp only [hash] <;> decide
  hD4 := by simp only [hash] <;> decide
  hN4 := by simp only [hash] <;> decide
  hDL := by simp only [hash] <;> decide
  hL4 := by simp only [hash] <;> decide
  hNL := by simp only [hash] <;> decide
  hso := by simp only [hash] <;> decide
  fits := by simp only [hash] <;> decide
  hW := by simp only [hash] <;> decide
  init := Proof.Sha256.X86_64.Stream.init_verified
  initDepth := by simp only [hash] <;> decide +kernel
  initSp := nosp_of (callees v).iNs
  updMx := Callees.updMx (callees v) coreOK
  finMx := Callees.finMx (callees v) coreOK
  updSp := Callees.updSp (callees v) coreOK
  finSp := Callees.finSp (callees v) coreOK
  updDepth := Callees.updD (callees v) coreOK
  finDepth := Callees.finD (callees v) coreOK

theorem satI : ∃ s, (Spec.Hmac.sha256I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha256I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] using initSat 96 104

theorem satF : ∃ s, (Spec.Hmac.sha256I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha256I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] using finSat 96 32 104

theorem satT : ∃ s, (Spec.Hmac.sha256I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha256I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi, X86_64.argRegs] using Pbkdf2.X86_64.iterSat 96 32 104

theorem satP : ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256S, Spec.Hmac.sha256, X86_64.abi,
    X86_64.argRegs] using pbkSat 200

/-- The streaming `update` and `finalize` made with `v`. -/
def stream : List StreamFn := [
  { api := Spec.Sha256.updateApi
    code := Impl.Sha256.X86_64.Stream.update v.callee
    contract := Spec.Sha256.updateContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha256.X86_64.Shared.update v.ok v.mxcsr
    spSafe := Proof.Sha256.X86_64.Shared.update_spSafe v.spSafe },
  { api := Spec.Sha256.finalizeApi
    code := Impl.Sha256.X86_64.Stream.finalize v.callee
    contract := Spec.Sha256.finalizeContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha256.X86_64.Shared.finalize v.ok v.mxcsr
    spSafe := Proof.Sha256.X86_64.Shared.finalize_spSafe v.spSafe }]

/-- SHA-256 with the implementation `v` of its compression function, which it
carries for the functions built on SHA-256 alone (`MdHash.sha256`). -/
def variant : MdHash :=
  { MdHash.of (ok v) coreOK (callees v) rfl rfl satI satF satT satP v.suffix v.features (stream v) with
    sha256 := some v }

end VG.Proof.Pbkdf2.Md.X86_64.Sha256
