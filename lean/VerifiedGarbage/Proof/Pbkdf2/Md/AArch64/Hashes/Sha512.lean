import VerifiedGarbage.Proof.Sha512.AArch64.Variant
import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Sha512
import VerifiedGarbage.Proof.Sha512.AArch64.Shared
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Spec.Sha512.Contract
import VerifiedGarbage.TCB.AArch64.Target

/-!
# The SHA-512 family on AArch64, as Merkle–Damgård hash functions

Untrusted: everything here is checked by Lean. SHA-384, SHA-512,
SHA-512/224 and SHA-512/256, with their compression function, as variants
of `MdHash` (`sha384`, …), from which HMAC and PBKDF2 are emitted
(`Generic/MdHash/AArch64/`). They share their streaming `update` and
`finalize` (`Impl/Sha512/AArch64/Stream.lean`) and differ in their initial
hash value `iv` and the size `D` of their digest, the first `D` bytes of the
final hash value. PBKDF2's iteration writes their length field and digest
with `Impl.Pbkdf2.AArch64.sha512` (`Proof/Pbkdf2/AArch64/Sha512.lean`). The
facts about the code HMAC and PBKDF2 add, which do not depend on the
functions they call, are checked once for each member (`coreOK`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha512

open VG.AArch64
open VG.Proof.Sha512.AArch64 (Compress)
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64 (updK finK)
open VG.Proof.Hmac.Generic.AArch64.Instances (initSat finSat)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`. -/
def hash (v : Compress) (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  P := Impl.Pbkdf2.AArch64.sha512
  D := D
  W := I.scratch
  compN := v.name
  compC := v.code
  initN := initN
  initC := Impl.Sha512.AArch64.Stream.init iv
  updN := Spec.Sha512.updateApi.name ++ v.suffix
  updC := v.update
  finN := Spec.Sha512.finalizeApi.name ++ v.suffix
  finC := v.finalize
  hmacInitN := I.initApi.name ++ v.suffix
  hmacFinN := I.finalizeApi.name ++ v.suffix
  iterN := I.iterateApi.name ++ v.suffix

/-- A member of the family without the functions it calls. -/
def coreH (D : Nat) : Hash :=
  ⟨Impl.Pbkdf2.AArch64.sha512, D, 234, "", .block [], "", .block [], "", .block [], "", .block [], "", "", ""⟩

theorem coreOK (D : Nat) (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) : CoreOK (coreH D) := by
  rcases hD with rfl | rfl | rfl | rfl <;> exact {
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
  }

/-- The initial hash values of the family. -/
abbrev IVs (iv : Spec.Sha512.HashValue) : Prop := iv = H0_384 ∨ iv = H0_512 ∨ iv = H0_512_224 ∨ iv = H0_512_256

/-- A state satisfying `updK`'s precondition at the family's sizes. -/
def updSat : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x30000 | .x4 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := [⟨0x30000, 0⟩]
  wr := [⟨0x10000, 192⟩, ⟨0x40000, 224⟩]

/-- A state satisfying `finK`'s precondition at the family's sizes. -/
def finKSat : State where
  gpr r := match r with
    | .x0 => 0x10000 | .x2 => 0x20000 | .x3 => 0x40000
    | _ => 0
  sp := 0x90000
  mem _ := 0
  rd := []
  wr := [⟨0x10000, 192⟩, ⟨0x20000, 64⟩, ⟨0x40000, 224⟩]

theorem upd_sat (R : Mem → Addr → List Byte → Prop) : ∃ s, (updK 192 224 R).pre s := by
  refine ⟨updSat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

theorem fin_sat (R : Mem → Addr → List Byte → Prop) (hash : List Byte → List Byte) (D : Nat) :
    ∃ s, (finK 192 224 64 D R hash).pre s := by
  refine ⟨finKSat, rfl, rfl, ?_, ?_, ?_, by decide, ?_, ?_, ?_⟩ <;>
    exact Region.disjoint_of_sep (by decide)

section
variable (v : Compress)
variable {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}

/-- The streaming functions of the member of instance `I`, verified against
the contracts HMAC's proofs call them with. -/
def streamOK (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hiv : IVs iv) :
    Hmac.Generic.AArch64.HashOK (hash v I D initN iv).stream where
  SH := I.S
  Wb := 224
  hS := hS
  hD := hDs
  hB := hB
  hDF := by show D ≤ 64; omega
  hF := Nat.le_refl 64
  hD0 := by show 0 < D; omega
  hS0 := show 0 < 192 by decide
  hSB := show 192 ≤ 256 by decide
  hB0 := show 0 < 128 by decide
  hBB := Nat.le_refl 128
  hWb := by show 224 ≤ 8 * ((Impl.Pbkdf2.AArch64.sha512.so + 48) / 8); decide
  hW := by show (Impl.Pbkdf2.AArch64.sha512.so + 48) / 8 ≤ 64; decide
  repr := hR ▸ Hmac.Generic.Common.sha512_repr iv
  init := hR ▸ Proof.Sha512.AArch64.Stream.init_verified iv
  upd := hR ▸ v.update_verified.of_implies
    { pre := fun _ ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := upd_sat _ }
  fin := v.finalize_verified.of_implies
    { pre := fun _ ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := fin_sat _ _ _ }
  initDepth := by
    show (Impl.Sha512.AArch64.Stream.init iv).fdepth ≤ 1
    rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  updDepth := by show v.update.fdepth ≤ 1; rw [show v.update.fdepth = 0 from v.updateDepth]; decide
  finDepth := by show v.finalize.fdepth ≤ 1; rw [show v.finalize.fdepth = 0 from v.finalizeDepth]; decide

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 234) (hiv : IVs iv) :
    HashOK (hash v I D initN iv) where
  initKeepsV := by rfl
  updKeepsV := v.updateKeepsV
  finKeepsV := v.finalizeKeepsV
  md := Proof.Sha512.md
  shape := Pbkdf2.AArch64.sha512_shape
  comp := ⟨v.verified.1, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  lenOk _ h := h
  stream := streamOK v hR hh hB hS hDs hD hiv
  iv := iv
  repr _ _ _ := by show I.S.Repr _ _ _ ↔ _; rw [hR]; exact Proof.Sha512.repr_iff
  hash := hh
  sizes := by
    show Pbkdf2.AArch64.Sizes Impl.Pbkdf2.AArch64.sha512 D I.scratch
    rw [hW]
    rcases hD with rfl | rfl | rfl | rfl <;>
    exact ⟨⟨by decide, by decide⟩, by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩
  L := by show 0 < Impl.Pbkdf2.AArch64.sha512.L ∧ Impl.Pbkdf2.AArch64.sha512.L ≤ 16; decide
  W := by show I.scratch ≤ 256; omega

end

/-- Streaming wrappers shared by all four digest sizes. The SHA-512 member
emits them once per backend through `MdHash`; the other members call them. -/
def stream (v : Compress) : List StreamFn := [
  { api := Spec.Sha512.updateApi
    code := v.update
    contract := Spec.Sha512.updateContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.update_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha512.finalizeApi
    code := v.finalize
    contract := Spec.Sha512.finalizeContract AArch64.abi
    verified := Proof.Sha512.AArch64.Shared.finalize_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-! ## SHA-384 -/

theorem sha384_satI : ∃ s, (Spec.Hmac.sha384I.initContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha384I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha384_satF : ∃ s, (Spec.Hmac.sha384I.finalizeContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha384I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using finSat 192 48 234

theorem sha384_satT : ∃ s, (Spec.Hmac.sha384I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha384I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 48 234

theorem sha384_satP : ∃ s, (Spec.Hmac.sha384I.pbkdf2Contract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha384I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha384S, Spec.Hmac.sha384, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha384_coreOK : CoreOK (coreH 48) := coreOK 48 (Or.inr (Or.inr (Or.inl rfl)))

/-- SHA-384 with its compression function. -/
def sha384 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl (Or.inl rfl)) sha384_coreOK rfl rfl
    sha384_satI sha384_satF sha384_satT sha384_satP v.suffix v.features

/-! ## SHA-512 -/

theorem sha512_satI : ∃ s, (Spec.Hmac.sha512I.initContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_satF : ∃ s, (Spec.Hmac.sha512I.finalizeContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using finSat 192 64 234

theorem sha512_satT : ∃ s, (Spec.Hmac.sha512I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 64 234

theorem sha512_satP : ∃ s, (Spec.Hmac.sha512I.pbkdf2Contract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512S, Spec.Hmac.sha512, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_coreOK : CoreOK (coreH 64) := coreOK 64 (Or.inr (Or.inr (Or.inr rfl)))

/-- SHA-512 with its compression function. -/
def sha512 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512)
    (ok v rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm) rfl rfl rfl (Or.inr (Or.inr (Or.inr rfl))) rfl (Or.inr (Or.inl rfl))) sha512_coreOK rfl rfl
    sha512_satI sha512_satF sha512_satT sha512_satP v.suffix v.features (stream v)

/-! ## SHA-512/224 -/

theorem sha512_224_satI : ∃ s, (Spec.Hmac.sha512_224I.initContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512_224I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_224_satF : ∃ s, (Spec.Hmac.sha512_224I.finalizeContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512_224I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using finSat 192 28 234

theorem sha512_224_satT : ∃ s, (Spec.Hmac.sha512_224I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_224I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 28 234

theorem sha512_224_satP : ∃ s, (Spec.Hmac.sha512_224I.pbkdf2Contract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_224I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_224_coreOK : CoreOK (coreH 28) := coreOK 28 (Or.inl rfl)

/-- SHA-512/224 with its compression function. -/
def sha512_224 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl (Or.inr (Or.inr (Or.inl rfl)))) sha512_224_coreOK rfl rfl
    sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP v.suffix v.features

/-! ## SHA-512/256 -/

theorem sha512_256_satI : ∃ s, (Spec.Hmac.sha512_256I.initContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha512_256I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using initSat 192 234

theorem sha512_256_satF : ∃ s, (Spec.Hmac.sha512_256I.finalizeContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha512_256I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using finSat 192 32 234

theorem sha512_256_satT : ∃ s, (Spec.Hmac.sha512_256I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha512_256I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi, AArch64.argRegs] using
    Pbkdf2.AArch64.iterSat 192 32 234

theorem sha512_256_satP : ∃ s, (Spec.Hmac.sha512_256I.pbkdf2Contract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha512_256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, AArch64.abi,
    AArch64.argRegs] using pbkSat 426

theorem sha512_256_coreOK : CoreOK (coreH 32) := coreOK 32 (Or.inr (Or.inl rfl))

/-- SHA-512/256 with its compression function. -/
def sha512_256 (v : Compress) : MdHash :=
  MdHash.of (H := hash v Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256)
    (ok v rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl (Or.inr (Or.inr (Or.inr rfl)))) sha512_256_coreOK rfl rfl
    sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP v.suffix v.features

end VG.Proof.Pbkdf2.Md.AArch64.Sha512
