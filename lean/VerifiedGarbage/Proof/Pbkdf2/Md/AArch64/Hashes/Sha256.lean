import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Variant
import VerifiedGarbage.Proof.Sha256.AArch64.Shared
import VerifiedGarbage.Proof.Sha256.AArch64.Variant
import VerifiedGarbage.Proof.Sha256.Md
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.TCB.AArch64.Target

/-!
# SHA-256 on AArch64, as a Merkle–Damgård hash function

SHA-256 with its compression function, as a variant of `MdHash` (`variant`),
from which HMAC and PBKDF2 are emitted (`Generic/MdHash/AArch64/`): its
streaming code is the generic Merkle–Damgård code (`Stream.params`), its
specification `Spec.Hmac.sha256S`. The facts about the code HMAC and PBKDF2
add, which do not depend on the functions they call, are checked once
(`coreOK`).
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Sha256

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Sha256.AArch64 (Compress)
open VG.Proof.Hmac.Generic.AArch64.Instances (initSat finSat)

/-- SHA-256's functions. -/
def hash (v : Compress) : Hash where
  P := Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params
  D := 32
  W := Spec.Hmac.sha256I.scratch
  compN := v.name
  compC := v.code
  initN := Spec.Sha256.initApi.name
  initC := Impl.Sha256.AArch64.Stream.init
  updN := Spec.Sha256.updateApi.name ++ v.suffix
  updC := v.update
  finN := Spec.Sha256.finalizeApi.name ++ v.suffix
  finC := v.finalize
  hmacInitN := Spec.Hmac.sha256I.initApi.name ++ v.suffix
  hmacFinN := Spec.Hmac.sha256I.finalizeApi.name ++ v.suffix
  iterN := Spec.Hmac.sha256I.iterateApi.name ++ v.suffix

/-- `hash` without the functions it calls. -/
def coreH : Hash := ⟨Impl.Pbkdf2.AArch64.ofMd Impl.Sha256.AArch64.Stream.params, 32, 104, "", .block [], "",
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
  hfin := ⟨⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩, ⟨_, by taint_decide⟩⟩
  fitI := by decide
  fitF := by decide

/-- The representation moves with the state's bytes. -/
theorem sha256_repr (m m' : Mem) (p q : Addr) (msg : List Byte)
    (h : ∀ i < 96, m' (q + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i))
    (hr : Spec.Sha256.Repr m p msg) : Spec.Sha256.Repr m' q msg := by
  refine ⟨?_, ?_⟩
  · rw [← hr.1]
    apply Vector.ext
    intro j hj
    simp only [Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc h (by omega)
  · rw [← hr.2]
    exact Hmac.Generic.Common.bytesAt_reloc h (o := 32) (k := msg.length % 64) (by omega)

variable (v : Compress)

/-- The streaming functions, verified against the contracts HMAC's proofs
call them with. -/
def streamOK : Hmac.Generic.AArch64.HashOK (hash v).stream where
  SH := Spec.Hmac.sha256S
  Wb := 160
  hS := rfl
  hD := rfl
  hB := rfl
  hDF := by simp only [hash, Hash.stream] <;> decide
  hF := by simp only [hash, Hash.stream] <;> decide
  hD0 := by simp only [hash, Hash.stream] <;> decide
  hS0 := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hSB := by simp only [hash, Hash.stream, Hash.S] <;> decide
  hB0 := by simp only [hash, Hash.stream] <;> decide
  hBB := by simp only [hash, Hash.stream] <;> decide
  hWb := by simp only [hash, Hash.stream] <;> decide
  hW := by simp only [hash, Hash.stream] <;> decide
  repr := sha256_repr
  init := Proof.Sha256.AArch64.Stream.init_verified
  upd := v.update_verified.of_implies
    { pre := fun _ h => h
      post := fun _ _ _ h m hr hc => h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.update_verified.2.2 }
  fin := v.finalize_verified.of_implies
    { pre := fun _ h => h
      post := fun s s' _ h m hr _ hc => by
        show List.take 32 (Spec.Sha256.bytesAt s'.mem _ 32) = _
        rw [List.take_of_length_le (by simp [Spec.Sha256.bytesAt])]
        exact h Spec.Sha256.H0 m hr hc
      pub := fun _ _ _ _ h => h
      sat := v.finalize_verified.2.2 }
  initDepth := by simp only [hash, Hash.stream] <;> decide +kernel
  updDepth := by
    show (Impl.MdStream.AArch64.update _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.update, Code.aarch64Depth, v.updateDepth]; decide
  finDepth := by
    show (Impl.MdStream.AArch64.finalize _ v.name v.code).aarch64Depth ≤ 1
    simp only [Impl.MdStream.AArch64.finalize, Code.aarch64Depth, v.finalizeDepth]; decide

def ok : HashOK (hash v) where
  initKeepsV := by rfl
  updKeepsV := MdStream.AArch64.update_keepsV v.keepsV
  finKeepsV := MdStream.AArch64.finalize_keepsV Proof.Sha256.AArch64.Stream.shape v.keepsV
  md := Proof.Sha256.md
  shape := Pbkdf2.AArch64.Shape.ofMd Proof.Sha256.AArch64.Stream.shape
  comp := ⟨v.callee.verified, v.verified.2.1, v.noFrames, v.keepsV⟩
  reloc m m' p q h := by
    apply Vector.ext
    intro j hj
    simp only [Proof.Sha256.md, Spec.Sha256.stateAt, Vector.getElem_ofFn]
    exact Hmac.Generic.Common.readW_reloc (n := 32) h (by omega)
  lenOk _ _ := trivial
  stream := streamOK v
  iv := Spec.Sha256.H0
  repr _ _ _ := Iff.rfl
  hash m := by
    show Spec.Sha256.hash m = _
    rw [Proof.Sha256.hash_eq]
    exact (List.take_of_length_le (Nat.le_of_eq (Proof.Sha256.md.digest_length _))).symm
  sizes := ⟨⟨by simp only [hash] <;> decide, by simp only [hash] <;> decide⟩,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide,
    by simp only [hash] <;> decide, by simp only [hash] <;> decide⟩
  L := by simp only [hash] <;> decide
  W := by simp only [hash] <;> decide

theorem satI : ∃ s, (Spec.Hmac.sha256I.initContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.initContract, Spec.Hmac.sha256I, Spec.Hmac.initContract, Spec.Hmac.initSig,
    Spec.Hmac.sha256S, Spec.Hmac.sha256, AArch64.abi, AArch64.argRegs] using initSat 96 104

theorem satF : ∃ s, (Spec.Hmac.sha256I.finalizeContract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.finalizeContract, Spec.Hmac.sha256I, Spec.Hmac.finalizeContract,
    Spec.Hmac.finalizeSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, AArch64.abi, AArch64.argRegs] using finSat 96 32 104

theorem satT : ∃ s, (Spec.Hmac.sha256I.iterateContract AArch64.abi).pre s := by
  inst_sat [Spec.Hmac.Instance.iterateContract, Spec.Hmac.sha256I, Spec.Pbkdf2.iterateContract,
    Spec.Pbkdf2.iterateSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, AArch64.abi, AArch64.argRegs]
    using Pbkdf2.AArch64.iterSat 96 32 104

theorem satP : ∃ s, (Spec.Hmac.sha256I.pbkdf2Contract AArch64.abi 16).pre s := by
  inst_sat [Spec.Hmac.Instance.pbkdf2Contract, Spec.Hmac.Instance.pbkdf2Scratch, Spec.Hmac.sha256I,
    Spec.Pbkdf2.pbkdf2Contract, Spec.Pbkdf2.pbkdf2Sig, Spec.Hmac.sha256S, Spec.Hmac.sha256, AArch64.abi,
    AArch64.argRegs] using pbkSat 200

/-- The streaming `update` and `finalize` made with `v`, which
`Generic/MdHash/AArch64/Stream.lean` emits. -/
def stream : List StreamFn := [
  { api := Spec.Sha256.updateApi
    code := v.update
    contract := Spec.Sha256.updateContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha256.AArch64.Shared.update_of v.update_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ },
  { api := Spec.Sha256.finalizeApi
    code := v.finalize
    contract := Spec.Sha256.finalizeContract AArch64.abi 16
    stack := 16
    verified := Proof.Sha256.AArch64.Shared.finalize_of v.finalize_verified
    spSafe := Code.all_of_forall (fun _ => rfl) _ }]

/-- Every construction follows the registered compression backend. -/
def variant : MdHash :=
  MdHash.of (ok v) coreOK rfl rfl satI satF satT satP v.suffix v.features (stream v)

end VG.Proof.Pbkdf2.Md.AArch64.Sha256
