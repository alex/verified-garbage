import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.PPC64LE.Inline
import VerifiedGarbage.Proof.Sha512.PPC64LE.Compress
import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Init
import VerifiedGarbage.Proof.Sha512.PPC64LE.Stream.Update
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on PPC64LE: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/PPC64LE/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.
-/

namespace VG.Proof.Sha512.PPC64LE.Shared

open _root_.VG.PPC64LE

/-- `compressPPC64LE` with 1328 bytes of scratch. -/
def compressWide : Contract PPC64LE.isa :=
  { Proof.Sha512.compressPPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 64⟩
      let blocks : Region := ⟨s.gpr .r4, 128 * (s.gpr .r5).toNat⟩
      let scratch : Region := ⟨s.gpr .r6, 1328⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch }

/-- `updatePPC64LE` with 1376 bytes of scratch. -/
def updateWide : Contract PPC64LE.isa :=
  { Proof.Sha512.updatePPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 192⟩
      let data : Region := ⟨s.gpr .r5, (s.gpr .r6).toNat⟩
      let scratch : Region := ⟨s.gpr .r7, 1376⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch }

/-- `finalizePPC64LE` with 1376 bytes of scratch. -/
def finalizeWide : Contract PPC64LE.isa :=
  { Proof.Sha512.finalizePPC64LE with
    pre := fun s =>
      let state : Region := ⟨s.gpr .r3, 192⟩
      let out : Region := ⟨s.gpr .r5, 64⟩
      let scratch : Region := ⟨s.gpr .r6, 1376⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub176 (a : Addr) : Region.Sub ⟨a, 176⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)
theorem sub224 (a : Addr) : Region.Sub ⟨a, 224⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.compress compressWide :=
  Verified.widen Proof.Sha512.PPC64LE.compress_verified
    (fun s => [⟨s.gpr .r3, 64⟩, ⟨s.gpr .r6, 176⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub176 _), h₄, h₅.sub_right (sub176 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.update updateWide :=
  Verified.widen Proof.Sha512.PPC64LE.Stream.Update.update_verified
    (fun s => [⟨s.gpr .r3, 192⟩, ⟨s.gpr .r7, 224⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃.sub_right (sub224 _), h₄, h₅.sub_right (sub224 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.PPC64LE.Stream.Finalize.finalize_verified
    (fun s => [⟨s.gpr .r3, 192⟩, ⟨s.gpr .r5, 64⟩, ⟨s.gpr .r6, 224⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅⟩ => ⟨h₁, rfl, h₃, h₄.sub_right (sub224 _), h₅.sub_right (sub224 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl)
      (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha512.PPC64LE.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.PPC64LE.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.PPC64LE.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compress :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.compress (Spec.Sha512.compressContract PPC64LE.abi) := by
  have hi : compressWide.Implies (Spec.Sha512.compressContract PPC64LE.abi) := by
    contract_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
      Proof.Sha512.compressPPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [compressSat, Proof.Sha512.PPC64LE.satState] using compressSat
  exact (compressWide_verified hi.sat_left).of_implies hi

theorem init (iv : Spec.Sha512.HashValue) :
    Verified PPC64LE.target (Impl.Sha512.PPC64LE.Stream.init iv) (Spec.Sha512.initContract PPC64LE.abi iv) :=
  (Proof.Sha512.PPC64LE.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initPPC64LE,
      PPC64LE.abi, PPC64LE.argRegs]
      [Proof.Sha512.PPC64LE.Stream.initSat] using Proof.Sha512.PPC64LE.Stream.initSat)

theorem update :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.update (Spec.Sha512.updateContract PPC64LE.abi) := by
  have hi : updateWide.Implies (Spec.Sha512.updateContract PPC64LE.abi) := by
    contract_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, updateWide,
      Proof.Sha512.updatePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [updateSat, Proof.Sha512.PPC64LE.Stream.Update.sat] using updateSat
  exact (updateWide_verified hi.sat_left).of_implies hi

theorem finalize :
    Verified PPC64LE.target Impl.Sha512.PPC64LE.Stream.finalize (Spec.Sha512.finalizeContract PPC64LE.abi) := by
  have hi : finalizeWide.Implies (Spec.Sha512.finalizeContract PPC64LE.abi) := by
    contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, finalizeWide,
      Proof.Sha512.finalizePPC64LE, PPC64LE.abi, PPC64LE.argRegs]
      [finalizeSat, Proof.Sha512.PPC64LE.Stream.Finalize.sat] using finalizeSat
  exact (finalizeWide_verified hi.sat_left).of_implies hi

end VG.Proof.Sha512.PPC64LE.Shared
