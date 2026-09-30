import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Variant
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Md
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Lit
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# The SHA-512 family on x86-64, as Merkle–Damgård hash functions

Untrusted: everything here is checked by Lean. SHA-384, SHA-512,
SHA-512/224 and SHA-512/256, with the one implementation of their
compression function, as variants of `MdHash`, from which HMAC and PBKDF2
are emitted (`Generic/MdHash/X86_64/`): their streaming code is the generic
Merkle–Damgård code (`Stream.params`), shared by the four, which differ in
their initial hash value `iv` and the size `D` of their digest, the first
`D` bytes of the final hash value. Their streaming functions are in their
registration file (`Artifacts/Sha512/X86_64.lean`).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Sha512

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64.Instances (initSat finSat)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`. -/
def hash (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  P := Impl.Sha512.X86_64.Stream.params
  D := D
  W := I.scratch
  compN := Spec.Sha512.compressApi.name
  compC := Impl.Sha512.X86_64.compress
  initN := initN
  initC := Impl.Sha512.X86_64.Stream.init iv
  updN := Spec.Sha512.updateApi.name
  finN := Spec.Sha512.finalizeApi.name
  hmacInitN := I.initApi.name
  hmacFinN := I.finalizeApi.name
  iterN := I.iterateApi.name

/-- A member of the family without the functions it calls. -/
def coreH (D : Nat) : Hash :=
  ⟨Impl.Sha512.X86_64.Stream.params, D, 96, "", .block [], "", .block [], "", "", "", "", ""⟩

theorem coreOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> exact {
      pbk := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
        ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
        ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
        ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
      iter := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩,
        ⟨_, by taint_decide⟩⟩
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

theorem callees {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue} (hiv : IVs iv) :
    Callees (hash I D initN iv) where
  cMx := by simp only [hash]; lit_decide
  cSp := by simp only [hash]; lit_decide
  cNs := by simp only [hash]; lit_decide
  cD := Proof.Sha512.X86_64.Stream.callee.depth
  iMx := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iSp := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iNs := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  iD := by simp only [hash]; rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}
    (C : CoreOK (core (hash I D initN iv))) (K : Callees (hash I D initN iv))
    (hR : I.S.Repr = Spec.Sha512.Repr iv) (hh : ∀ m, I.S.H.hash m = (Proof.Sha512.md.hash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 96) : HashOK (hash I D initN iv) where
  md := Proof.Sha512.md
  dims := Proof.Sha512.X86_64.Stream.dims
  shape := Proof.Sha512.X86_64.Stream.shape
  taints := Proof.Sha512.X86_64.Stream.taints
  comp := Proof.Sha512.X86_64.Stream.callee
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
  fits := by show 176 + 48 + 64 + 128 ≤ 8 * I.scratch; omega
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

/-! ## SHA-384 -/

theorem sha384_satI : ∃ s, (Spec.Hmac.sha384I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha384I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using initSat 192 96

theorem sha384_satF : ∃ s, (Spec.Hmac.sha384I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha384I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using finSat 192 48 96

theorem sha384_satT : ∃ s, (Spec.Hmac.sha384I.iterateContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha384I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi, X86_64.argRegs] using iterSat 192 48 96

theorem sha384_satP : ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha384S, Spec.Hmac.sha384, X86_64.abi,
    X86_64.argRegs] using pbkSat 288

/-- SHA-384, as a variant of `MdHash`. -/
def sha384 : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384)) := coreOK 48 (Or.inr (Or.inr (Or.inl rfl)))
  have K : Callees (hash Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384) := callees (Or.inl rfl)
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl) C K rfl rfl (by decide) sha384_satI sha384_satF sha384_satT sha384_satP
    "" [] []

/-! ## SHA-512 -/

theorem sha512_satI : ∃ s, (Spec.Hmac.sha512I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using initSat 192 96

theorem sha512_satF : ∃ s, (Spec.Hmac.sha512I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using finSat 192 64 96

theorem sha512_satT : ∃ s, (Spec.Hmac.sha512I.iterateContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi, X86_64.argRegs] using iterSat 192 64 96

theorem sha512_satP : ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512S, Spec.Hmac.sha512, X86_64.abi,
    X86_64.argRegs] using pbkSat 288

/-- SHA-512, as a variant of `MdHash`. -/
def sha512 : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512)) := coreOK 64 (Or.inr (Or.inr (Or.inr rfl)))
  have K : Callees (hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512) := callees (Or.inr (Or.inl rfl))
  MdHash.of (ok C K rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (Proof.Sha512.md.digest_length _))).symm) rfl rfl rfl (Or.inr (Or.inr (Or.inr rfl))) rfl) C K rfl rfl (by decide) sha512_satI sha512_satF sha512_satT sha512_satP
    "" [] []

/-! ## SHA-512/224 -/

theorem sha512_224_satI : ∃ s, (Spec.Hmac.sha512_224I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512_224I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using initSat 192 96

theorem sha512_224_satF : ∃ s, (Spec.Hmac.sha512_224I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512_224I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using finSat 192 28 96

theorem sha512_224_satT : ∃ s, (Spec.Hmac.sha512_224I.iterateContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_224I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi, X86_64.argRegs] using iterSat 192 28 96

theorem sha512_224_satP : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, X86_64.abi,
    X86_64.argRegs] using pbkSat 288

/-- SHA-512/224, as a variant of `MdHash`. -/
def sha512_224 : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224)) := coreOK 28 (Or.inl rfl)
  have K : Callees (hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224) := callees (Or.inr (Or.inr (Or.inl rfl)))
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl) C K rfl rfl (by decide) sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP
    "" [] []

/-! ## SHA-512/256 -/

theorem sha512_256_satI : ∃ s, (Spec.Hmac.sha512_256I.initContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512_256I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using initSat 192 96

theorem sha512_256_satF : ∃ s, (Spec.Hmac.sha512_256I.finalizeContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512_256I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using finSat 192 32 96

theorem sha512_256_satT : ∃ s, (Spec.Hmac.sha512_256I.iterateContract X86_64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_256I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi, X86_64.argRegs] using iterSat 192 32 96

theorem sha512_256_satP : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract X86_64.abi 24).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, X86_64.abi,
    X86_64.argRegs] using pbkSat 288

/-- SHA-512/256, as a variant of `MdHash`. -/
def sha512_256 : MdHash :=
  have C : CoreOK (core (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256)) := coreOK 32 (Or.inr (Or.inl rfl))
  have K : Callees (hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256) := callees (Or.inr (Or.inr (Or.inr rfl)))
  MdHash.of (ok C K rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl) C K rfl rfl (by decide) sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP
    "" [] []

end VG.Proof.Pbkdf2.Md.X86_64.Sha512
