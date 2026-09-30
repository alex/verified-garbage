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
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64 (updK finK)
open VG.Proof.Hmac.Generic.AArch64.Instances (initSat finSat)
open Spec.Sha512 (H0_384 H0_512 H0_512_224 H0_512_256)

/-- The member of the SHA-512 family of instance `I`, with a `D`-byte digest,
initial hash value `iv` and streaming `init` named `initN`. -/
def hash (I : Spec.Hmac.Instance) (D : Nat) (initN : String) (iv : Spec.Sha512.HashValue) : Hash where
  P := Impl.Pbkdf2.AArch64.sha512
  D := D
  W := I.scratch
  compN := Spec.Sha512.compressApi.name
  compC := Impl.Sha512.AArch64.compress
  initN := initN
  initC := Impl.Sha512.AArch64.Stream.init iv
  updN := Spec.Sha512.updateApi.name
  updC := Impl.Sha512.AArch64.Stream.update
  finN := Spec.Sha512.finalizeApi.name
  finC := Impl.Sha512.AArch64.Stream.finalize
  hmacInitN := I.initApi.name
  hmacFinN := I.finalizeApi.name
  iterN := I.iterateApi.name

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

theorem update_depth : Impl.Sha512.AArch64.Stream.update.fdepth ≤ 1 := by decide +kernel
theorem finalize_depth : Impl.Sha512.AArch64.Stream.finalize.fdepth ≤ 1 := by decide +kernel

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
variable {I : Spec.Hmac.Instance} {D : Nat} {initN : String} {iv : Spec.Sha512.HashValue}

/-- The streaming functions of the member of instance `I`, verified against
the contracts HMAC's proofs call them with. -/
def streamOK (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hiv : IVs iv) :
    Hmac.Generic.AArch64.HashOK (hash I D initN iv).stream where
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
  upd := hR ▸ Proof.Sha512.AArch64.Stream.Update.update_verified.of_implies
    { pre := fun _ ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩
      post := fun _ _ _ h m hr hc => h iv m hr hc
      pub := fun _ _ _ _ h => h
      sat := upd_sat _ }
  fin := Proof.Sha512.AArch64.Stream.Finalize.finalize_verified.of_implies
    { pre := fun _ ⟨a, b, c, d, e, _⟩ => ⟨a, b, c, d, e⟩
      post := fun s s' _ h m hr hl hc => by
        show List.take D (Spec.Sha512.bytesAt s'.mem _ 64) = _
        rw [hh, h iv m (hR ▸ hr) hl hc]
      pub := fun _ _ _ _ h => h
      sat := fin_sat _ _ _ }
  initDepth := by
    show (Impl.Sha512.AArch64.Stream.init iv).fdepth ≤ 1
    rcases hiv with rfl | rfl | rfl | rfl <;> decide +kernel
  updDepth := update_depth
  finDepth := finalize_depth

/-- `HashOK` for the member of instance `I`, whose specification is the
family's from `iv`, with its digest the first `D` bytes. -/
def ok (hR : I.S.Repr = Spec.Sha512.Repr iv)
    (hh : ∀ m, I.S.H.hash m = (Spec.Sha512.finalHash iv m).take D)
    (hB : I.S.H.blockSize = 128) (hS : I.S.stateBytes = 192) (hDs : I.S.digestBytes = D)
    (hD : D = 28 ∨ D = 32 ∨ D = 48 ∨ D = 64) (hW : I.scratch = 234) (hiv : IVs iv) :
    HashOK (hash I D initN iv) where
  md := Proof.Sha512.md
  shape := Pbkdf2.AArch64.sha512_shape
  comp := ⟨Proof.Sha512.AArch64.compress_verified.1, Proof.Sha512.AArch64.compress_verified.2.1,
    by show Impl.Sha512.AArch64.compress.noFrames = true; lit_decide⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha512.md, Spec.Sha512.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 64) h (by omega)
  lenOk _ h := h
  stream := streamOK hR hh hB hS hDs hD hiv
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
def sha384 : MdHash :=
  MdHash.of (H := hash Spec.Hmac.sha384I 48 Spec.Sha512.init384Api.name H0_384)
    (ok rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inr (Or.inl rfl))) rfl (Or.inl rfl)) sha384_coreOK rfl rfl
    sha384_satI sha384_satF sha384_satT sha384_satP "" []

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
def sha512 : MdHash :=
  MdHash.of (H := hash Spec.Hmac.sha512I 64 Spec.Sha512.init512Api.name H0_512)
    (ok rfl (fun m => (List.take_of_length_le (Nat.le_of_eq (Hmac.Generic.Common.finalHash_length _ m))).symm) rfl rfl rfl (Or.inr (Or.inr (Or.inr rfl))) rfl (Or.inr (Or.inl rfl))) sha512_coreOK rfl rfl
    sha512_satI sha512_satF sha512_satT sha512_satP "" []

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
def sha512_224 : MdHash :=
  MdHash.of (H := hash Spec.Hmac.sha512_224I 28 Spec.Sha512.init512_224Api.name H0_512_224)
    (ok rfl (fun _ => rfl) rfl rfl rfl (Or.inl rfl) rfl (Or.inr (Or.inr (Or.inl rfl)))) sha512_224_coreOK rfl rfl
    sha512_224_satI sha512_224_satF sha512_224_satT sha512_224_satP "" []

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
def sha512_256 : MdHash :=
  MdHash.of (H := hash Spec.Hmac.sha512_256I 32 Spec.Sha512.init512_256Api.name H0_512_256)
    (ok rfl (fun _ => rfl) rfl rfl rfl (Or.inr (Or.inl rfl)) rfl (Or.inr (Or.inr (Or.inr rfl)))) sha512_256_coreOK rfl rfl
    sha512_256_satI sha512_256_satF sha512_256_satT sha512_256_satP "" []

end VG.Proof.Pbkdf2.Md.AArch64.Sha512
