import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Sha512.X86_64.Variant
import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.TCB.X86_64.Target

/-!
# The SHA-512 family on x86-64, as Merkle–Damgård hash functions

Untrusted: everything here is checked by Lean. SHA-384, SHA-512,
SHA-512/224 and SHA-512/256, each with an implementation `v` of their
compression function (`Proof/Sha512/X86_64/Variant.lean`), as variants of
`MdHash` (`sha384 v`, …), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/X86_64/`): their streaming code is the generic
Merkle–Damgård code (`Stream.params`), shared by the four, which differ in
their initial hash value `iv` and the size `D` of their digest, the first
`D` bytes of the final hash value. The facts about the code HMAC and PBKDF2
add, which do not depend on `v`, are checked once for each member
(`coreOK`).

`stream v` are the streaming `update` and `finalize` made with `v`, which
the four share: SHA-512's variant (`sha512 v`) carries them, and
`Generic/MdHash/X86_64/Stream.lean` emits them from their `Api`s, named
with its suffix.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha512

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Sha512.X86_64 (Compress)
open VG.Proof.Hmac.Generic.X86_64.Instances (initSat finSat)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`, calling the
implementation `v` of the compression function, named with its suffix. -/
def hash (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) (v : Compress) :
    Hash where
  P := Impl.Sha512.X86_64.Stream.params
  D := D
  W := I.scratch
  compN := v.callee.name
  compC := v.callee.code
  initN := initN
  initC := Impl.Sha512.X86_64.Stream.init iv
  updN := Spec.Sha512.updateApi.name ++ v.suffix
  finN := Spec.Sha512.finalizeApi.name ++ v.suffix
  hmacInitN := I.initApi.name ++ v.suffix
  hmacFinN := I.finalizeApi.name ++ v.suffix
  iterN := I.iterateApi.name ++ v.suffix

/-- A member of the family without the functions it calls, the same for
every `v`. -/
def coreH (D : Nat) : Hash :=
  ⟨Impl.Sha512.X86_64.Stream.params, D, 234, "", .block [], "", .block [], "", "", "", "", ""⟩

theorem coreOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> exact {
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
      hfin := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
        ⟨_, by taint_decide⟩⟩
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
  }

/-- The initial hash values of the family. -/
abbrev IVs (iv : Spec.Sha512.HashValue) : Prop := iv = H0_384 ∨ iv = H0_512 ∨ iv = H0_512_224 ∨ iv = H0_512_256

theorem callees {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} (hiv : IVs iv)
    (v : Compress) : Callees (hash I D initN iv v) where
  cMx := v.mxcsr
  cSp := allInstrs_of_all v.spSafe
  cNs := by
    show v.callee.code.allInstrs _ = true
    rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by simp [v.ok.nosp i hi]
  cD := v.ok.depth
  iMx := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iSp := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iNs := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iD := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} {v : Compress}
    (C : CoreOK (core (hash I D initN iv v))) (K : Callees (hash I D initN iv v))
    (hR : I.S.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, I.S.H.hash m = (Proof.Sha512.md.hash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 234) : HashOK (hash I D initN iv v) where
  md := Proof.Sha512.md
  dims := Proof.Sha512.X86_64.Stream.dims
  shape := Proof.Sha512.X86_64.Stream.shape
  taints := Proof.Sha512.X86_64.Stream.taints
  comp := v.ok
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  lenOk _ h := h
  SH := I.S
  iv := iv
  repr _ _ _ := by rw [hR]; exact Proof.Sha512.repr_iff
  hash := hh
  hB := hB
  hS := hS
  hD := hDs
  hD0 := by show 0 < D; omega
  hDN := by show D ≤ 64; omega
  hD4 := by show D % 4 = 0; omega
  hN4 := by simp only [hash] <;> decide
  hDL := by show D + 16 + 4 ≤ 128; omega
  hL4 := by simp only [hash] <;> decide
  hNL := by simp only [hash] <;> decide
  hso := by simp only [hash] <;> decide
  fits := by show 1328 + 48 + 64 + 128 ≤ 8 * I.scratch; omega
  hW := by show I.scratch ≤ 256; omega
  init := hR ▸ Proof.Sha512.X86_64.Stream.init_verified iv
  initDepth := by rw [K.iD]; decide
  initSp := nosp_of K.iNs
  updMx := Callees.updMx K C
  finMx := Callees.finMx K C
  updSp := Callees.updSp K C
  finSp := Callees.finSp K C
  updDepth := Callees.updD K C
  finDepth := Callees.finD K C

/-- The streaming `update` and `finalize` made with `v`, which the family
shares. -/
def stream (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.updateApi
    code := Impl.Sha512.X86_64.Stream.update v.callee
    contract := Spec.Sha512.updateContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha512.X86_64.Shared.update v.ok v.mxcsr
    spSafe := Proof.Sha512.X86_64.Shared.update_spSafe v.spSafe },
  { api := Spec.Sha512.finalizeApi
    code := Impl.Sha512.X86_64.Stream.finalize v.callee
    contract := Spec.Sha512.finalizeContract X86_64.abi 8
    stack := 8
    verified := Proof.Sha512.X86_64.Shared.finalize v.ok v.mxcsr
    spSafe := Proof.Sha512.X86_64.Shared.finalize_spSafe v.spSafe }]

/-! ## SHA-384 -/

theorem sha384_satI : ∃ s, (Spec.Hmac.sha384I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha384I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha384_satF : ∃ s, (Spec.Hmac.sha384I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha384I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using finSat 192 48 234

theorem sha384_satT : ∃ s, (Spec.Hmac.sha384I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha384I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 48 234

theorem sha384_satP : ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha384_coreOK : CoreOK (coreH 48) := coreOK 48 (Or.inr (Or.inr (Or.inl rfl)))

/-- SHA-384 with the implementation `v` of the compression function. -/
def sha384 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384 v)) := sha384_coreOK
  have K : Callees (hash Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384 v) := callees (Or.inl rfl) v
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl) C K rfl rfl
    sha384_satI sha384_satF sha384_satT sha384_satP v.suffix v.features stream

/-! ## SHA-512 -/

theorem sha512_satI : ∃ s, (Spec.Hmac.sha512I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_satF : ∃ s, (Spec.Hmac.sha512I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using finSat 192 64 234

theorem sha512_satT : ∃ s, (Spec.Hmac.sha512I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 64 234

theorem sha512_satP : ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_coreOK : CoreOK (coreH 64) := coreOK 64 (Or.inr (Or.inr (Or.inr rfl)))

/-- SHA-512 with the implementation `v` of the compression function. -/
def sha512 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512 v)) := sha512_coreOK
  have K : Callees (hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512 v) := callees (Or.inr (Or.inl rfl)) v
  MdHash.of (ok C K rfl (fun _ => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))).symm) rfl rfl rfl (Or.inr (Or.inr (Or.inr rfl))) rfl) C K rfl rfl
    sha512_satI sha512_satF sha512_satT sha512_satP v.suffix v.features stream

/-! ## SHA-512/224 -/

theorem sha512_224_satI : ∃ s, (Spec.Hmac.sha512_224I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512_224I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_224_satF : ∃ s, (Spec.Hmac.sha512_224I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512_224I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using finSat 192 28 234

theorem sha512_224_satT : ∃ s, (Spec.Hmac.sha512_224I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_224I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 28 234

theorem sha512_224_satP : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_224_coreOK : CoreOK (coreH 28) := coreOK 28 (Or.inl rfl)

/-- SHA-512/224 with the implementation `v` of the compression function. -/
def sha512_224 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224 v)) := sha512_224_coreOK
  have K : Callees (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224 v) := callees (Or.inr (Or.inr (Or.inl rfl))) v
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl) C K rfl rfl
    sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP v.suffix v.features stream

/-! ## SHA-512/256 -/

theorem sha512_256_satI : ∃ s, (Spec.Hmac.sha512_256I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512_256I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using initSat 192 234

theorem sha512_256_satF : ∃ s, (Spec.Hmac.sha512_256I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512_256I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using finSat 192 32 234

theorem sha512_256_satT : ∃ s, (Spec.Hmac.sha512_256I.iterateContract X86_64.abi 8).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_256I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using
    Pbkdf2.X86_64.iterSat 192 32 234

theorem sha512_256_satP : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs] using pbkSat 426

theorem sha512_256_coreOK : CoreOK (coreH 32) := coreOK 32 (Or.inr (Or.inl rfl))

/-- SHA-512/256 with the implementation `v` of the compression function. -/
def sha512_256 (v : Compress) (stream : List StreamFn := []) : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256 v)) := sha512_256_coreOK
  have K : Callees (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256 v) := callees (Or.inr (Or.inr (Or.inr rfl))) v
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl) C K rfl rfl
    sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP v.suffix v.features stream

end VG.Proof.Pbkdf2.Md.X86_64.Sha512
