import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Sha256.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Finalize
import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Init
import VerifiedGarbage.Proof.Sha256.PPC64LE.Stream.Update
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# Sha256 on PPC64LE: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/PPC64LE/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (560
bytes for `compress`, 608 for `update` and `finalize`, sized for x86-64's AVX2
compression function): the per-target contracts are first widened to that
scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.
-/

namespace VG.Proof.Sha256.PPC64LE.Shared

open _root_.VG.PPC64LE

/-- `compressPPC64LE` with 560 bytes of scratch. -/
def compressWide : Contract PPC64LE.isa :=
  { Proof.Sha256.compressPPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 32⟩
      let blocks : Region := ⟨s.gpr .r4, 64 * (s.gpr .r5).toNat⟩
      let scratch : Region := ⟨s.gpr .r6, 560⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

/-- `updatePPC64LE` with 608 bytes of scratch. -/
def updateWide : Contract PPC64LE.isa :=
  { Proof.Sha256.updatePPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 96⟩
      let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
      let scratch : Region := ⟨s.gpr .r7, 608⟩
      let stack : Region := ⟨s.sp - 48, 48⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch }

/-- `finalizePPC64LE` with 608 bytes of scratch. -/
def finalizeWide : Contract PPC64LE.isa :=
  { Proof.Sha256.finalizePPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 96⟩
      let out : Region := ⟨s.gpr .r5, 32⟩
      let scratch : Region := ⟨s.gpr .r6, 608⟩
      let stack : Region := ⟨s.sp - 48, 48⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      48 ≤ s.sp.toNat ∧ stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 560⟩ := Region.sub_prefix (by decide)
theorem sub160 (a : Addr) : Region.Sub ⟨a, 160⟩ ⟨a, 608⟩ := Region.sub_prefix (by decide)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.compress compressWide :=
  Verified.widen Proof.Sha256.PPC64LE.compress_verified
    (fun s => [⟨s.gpr .r3, 32⟩, ⟨s.gpr .r6, 112⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.update updateWide :=
  Verified.widen Proof.Sha256.PPC64LE.Stream.Update.update_verified
    (fun s => [⟨s.gpr .r3, 96⟩, ⟨s.gpr .r7, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub160 _), h₄, h₅.sub_right (sub160 _), h₆, h₇, h₈,
        h₉.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha256.PPC64LE.Stream.Finalize.finalize_verified
    (fun s => [⟨s.gpr .r3, 96⟩, ⟨s.gpr .r5, 32⟩, ⟨s.gpr .r6, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇, h₈,
        h₉.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha256.PPC64LE.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha256.PPC64LE.Stream.Update.sat with wr := [⟨0x1000, 96⟩, ⟨0x3000, 608⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha256.PPC64LE.Stream.Finalize.sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 608⟩] }

theorem compress :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.compress (Spec.Sha256.compressContract PPC64LE.abi) := by
  have hi : compressWide.Implies (Spec.Sha256.compressContract PPC64LE.abi) := by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, compressWide,
      Proof.Sha256.compressPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [compressSat, Proof.Sha256.PPC64LE.satState] using compressSat
  exact (compressWide_verified hi.sat_left).of_implies hi

theorem init :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.init (Spec.Sha256.initContract PPC64LE.abi) :=
  Proof.Sha256.PPC64LE.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha256.PPC64LE.Stream.initSat] using Proof.Sha256.PPC64LE.Stream.initSat)

theorem update :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.update (Spec.Sha256.updateContract PPC64LE.abi 48) := by
  have hi : updateWide.Implies (Spec.Sha256.updateContract PPC64LE.abi 48) := by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, updateWide,
      Proof.Sha256.updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [updateSat, Proof.Sha256.PPC64LE.Stream.Update.sat] using updateSat
  exact (updateWide_verified hi.sat_left).of_implies hi

theorem finalize :
    Verified PPC64LE.target Impl.Sha256.PPC64LE.Stream.finalize (Spec.Sha256.finalizeContract PPC64LE.abi 48) := by
  have hi : finalizeWide.Implies (Spec.Sha256.finalizeContract PPC64LE.abi 48) := by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, finalizeWide,
      Proof.Sha256.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [finalizeSat, Proof.Sha256.PPC64LE.Stream.Finalize.sat] using finalizeSat
  exact (finalizeWide_verified hi.sat_left).of_implies hi

end VG.Proof.Sha256.PPC64LE.Shared
