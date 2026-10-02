import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Sha512.AArch64.Compress
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Init
import VerifiedGarbage.Proof.Sha512.AArch64.Stream.Md
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on AArch64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha512/AArch64/Compress.lean`); these theorems move them to the shared
contracts of `Spec/Sha512/Contract.lean`, which the artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.
-/

namespace VG.Proof.Sha512.AArch64.Shared

open _root_.VG.AArch64

/-- `compressAArch64` with 1328 bytes of scratch. -/
def compressWide : Contract AArch64.isa :=
  { Proof.Sha512.compressAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 64⟩
      let blocks : Region := ⟨s.gpr .x1, 128 * (s.gpr .x2).toNat⟩
      let scratch : Region := ⟨s.gpr .x3, 1328⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

/-- `updateAArch64` with 1376 bytes of scratch. -/
def updateWide : Contract AArch64.isa :=
  { Proof.Sha512.updateAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 192⟩
      let data : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
      let scratch : Region := ⟨s.gpr .x4, 1376⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch }

/-- `finalizeAArch64` with 1376 bytes of scratch. -/
def finalizeWide : Contract AArch64.isa :=
  { Proof.Sha512.finalizeAArch64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .x0, 192⟩
      let out : Region := ⟨s.gpr .x2, 64⟩
      let scratch : Region := ⟨s.gpr .x3, 1376⟩
      let stack : Region := ⟨s.sp - 16, 16⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      16 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem subC (a : Addr) : Region.Sub ⟨a, Impl.Sha512.AArch64.scratchBytes⟩ ⟨a, 1328⟩ :=
  Region.sub_prefix (by decide)
theorem subS (a : Addr) : Region.Sub ⟨a, Impl.Sha512.AArch64.scratchBytes + 48⟩ ⟨a, 1376⟩ :=
  Region.sub_prefix (by decide)

theorem compressWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.compressAArch64) (hsat : ∃ s, compressWide.pre s) :
    Verified AArch64.target code compressWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 64⟩, ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (subC _), h₄, h₅.sub_right (subC _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) (hsat : ∃ s, updateWide.pre s) :
    Verified AArch64.target code updateWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 192⟩, ⟨s.gpr .x4, Impl.Sha512.AArch64.scratchBytes + 48⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃.sub_right (subS _), h₄, h₅.sub_right (subS _), h₆, h₇, h₈,
        h₉.sub_right (subS _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) (hsat : ∃ s, finalizeWide.pre s) :
    Verified AArch64.target code finalizeWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .x0, 192⟩, ⟨s.gpr .x2, 64⟩, ⟨s.gpr .x3, Impl.Sha512.AArch64.scratchBytes + 48⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (subS _), h₅.sub_right (subS _), h₆, h₇, h₈,
        h₉.sub_right (subS _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl)
      (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha512.AArch64.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.AArch64.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.AArch64.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compress_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.compressAArch64) :
    Verified AArch64.target code (Spec.Sha512.compressContract AArch64.abi) := by
  have hi : compressWide.Implies (Spec.Sha512.compressContract AArch64.abi) := by
    sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
      Proof.Sha512.compressAArch64, AArch64.abi, AArch64.argRegs]
      [compressSat, Proof.Sha512.AArch64.satState] using compressSat
  exact (compressWide_of hv hi.sat_left).of_implies hi

theorem init (iv : Spec.Sha512.HashValue) :
    Verified AArch64.target (Impl.Sha512.AArch64.Stream.init iv) (Spec.Sha512.initContract AArch64.abi iv) :=
  (Proof.Sha512.AArch64.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initAArch64,
      AArch64.abi, AArch64.argRegs]
      [Proof.Sha512.AArch64.Stream.initSat] using Proof.Sha512.AArch64.Stream.initSat)

theorem update_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.updateAArch64) :
    Verified AArch64.target code (Spec.Sha512.updateContract AArch64.abi 16) := by
  have hi : updateWide.Implies (Spec.Sha512.updateContract AArch64.abi 16) := by
    contract_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, updateWide,
      Proof.Sha512.updateAArch64, AArch64.abi, AArch64.argRegs]
      [updateSat, Proof.Sha512.AArch64.Stream.Update.sat, MdStream.AArch64.Update.sat,
        Impl.Sha512.AArch64.Stream.params] using updateSat
  exact (updateWide_of hv hi.sat_left).of_implies hi

theorem finalize_of {code : Prog isa} (hv : Verified AArch64.target code Proof.Sha512.finalizeAArch64) :
    Verified AArch64.target code (Spec.Sha512.finalizeContract AArch64.abi 16) := by
  have hi : finalizeWide.Implies (Spec.Sha512.finalizeContract AArch64.abi 16) := by
    contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, finalizeWide,
      Proof.Sha512.finalizeAArch64, AArch64.abi, AArch64.argRegs]
      [finalizeSat, Proof.Sha512.AArch64.Stream.Finalize.sat, MdStream.AArch64.Finalize.sat,
        Impl.Sha512.AArch64.Stream.params] using finalizeSat
  exact (finalizeWide_of hv hi.sat_left).of_implies hi

theorem compress : Verified AArch64.target Impl.Sha512.AArch64.compress (Spec.Sha512.compressContract AArch64.abi) :=
  compress_of Proof.Sha512.AArch64.compress_verified

end VG.Proof.Sha512.AArch64.Shared
