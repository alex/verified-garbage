import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Sha256.Arm.Compress
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha256.Arm.Stream.Md
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# Sha256 on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/Arm/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (560
bytes for `compress`, 608 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.
-/

namespace VG.Proof.Sha256.Arm.Shared

open _root_.VG.Arm

/-- `compressArm` with 560 bytes of scratch. -/
def compressWide : Contract Arm.isa :=
  { Proof.Sha256.compressArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 32⟩
      let blocks : Region := ⟨State.addr (s.gpr .r1), 64 * (s.gpr .r2).toNat⟩
      let scratch : Region := ⟨State.addr (s.gpr .r3), 560⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      (s.gpr .r0).toNat + 32 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 560 ≤ 2 ^ 32 }

/-- `updateArm` with 608 bytes of scratch. -/
def updateWide : Contract Arm.isa :=
  { Proof.Sha256.updateArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 96⟩
      let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
      let scratch : Region := ⟨State.addr (stackArg s 2), 608⟩
      let args : Region := ⟨stackArgAddr s 0, 12⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 608 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32 }

/-- `finalizeArm` with 608 bytes of scratch. -/
def finalizeWide : Contract Arm.isa :=
  { Proof.Sha256.finalizeArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 96⟩
      let out : Region := ⟨State.addr (stackArg s 0), 32⟩
      let scratch : Region := ⟨State.addr (stackArg s 1), 608⟩
      let args : Region := ⟨stackArgAddr s 0, 8⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 96 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 32 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 608 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 560⟩ := Region.sub_prefix (by decide)
theorem sub160 (a : Addr) : Region.Sub ⟨a, 160⟩ ⟨a, 608⟩ := Region.sub_prefix (by decide)
theorem le112 {x : Nat} (h : x + 560 ≤ 2 ^ 32) : x + 112 ≤ 2 ^ 32 := by omega
theorem le160 {x : Nat} (h : x + 608 ≤ 2 ^ 32) : x + 160 ≤ 2 ^ 32 := by omega

/-- Rewrites the per-target contracts at a narrowed state (`stackArg` does
not unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sha256.compressArm, Proof.Sha256.updateArm, Proof.Sha256.finalizeArm,
    Proof.Sha256.countArm, compressWide, updateWide, finalizeWide, VG.Arm.stackArg_withRegions,
    VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem,
    State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified Arm.target Impl.Sha256.Arm.compress compressWide :=
  Verified.widen Proof.Sha256.Arm.compress_verified
    (fun s => [⟨State.addr (s.gpr .r0), 32⟩, ⟨State.addr (s.gpr .r3), 112⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _), h₆, h₇, le112 h₈⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified Arm.target Impl.Sha256.Arm.Stream.update updateWide :=
  Verified.widen Proof.Sha256.Arm.Stream.Update.update_verified
    (fun s => [⟨State.addr (s.gpr .r0), 96⟩, ⟨State.addr (stackArg s 2), 160⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub160 _), h₄, h₅.sub_right (sub160 _), h₆,
        h₇.sub_right (sub160 _), h₈, h₉, le160 h₁₀, h₁₁⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha256.Arm.Stream.Finalize.finalize_verified
    (fun s => [⟨State.addr (s.gpr .r0), 96⟩, ⟨State.addr (stackArg s 0), 32⟩,
      ⟨State.addr (stackArg s 1), 160⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇,
        h₈.sub_right (sub160 _), h₉, h₁₀, le160 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha256.Arm.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State := { Proof.Sha256.Arm.Stream.Update.sat with wr := [⟨0x1000, 96⟩, ⟨0, 608⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha256.Arm.Stream.Finalize.sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 608⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha256.compressContract Arm.abi) := by
  contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, compressWide,
    Proof.Sha256.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [compressSat, Proof.Sha256.Arm.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using compressSat

theorem compress :
    Verified Arm.target Impl.Sha256.Arm.compress (Spec.Sha256.compressContract Arm.abi) :=
  (compressWide_verified compressWide_implies.sat_left).of_implies compressWide_implies

theorem init : Verified Arm.target Impl.Sha256.Arm.Stream.init (Spec.Sha256.initContract Arm.abi) :=
  Proof.Sha256.Arm.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha256.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha256.Arm.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha256.updateContract Arm.abi) := by
  contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, updateWide,
    Proof.Sha256.updateArm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [updateSat, Proof.Sha256.Arm.Stream.Update.sat, MdStream.Arm.Update.sat,
    Impl.Sha256.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using updateSat

theorem update :
    Verified Arm.target Impl.Sha256.Arm.Stream.update (Spec.Sha256.updateContract Arm.abi) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha256.finalizeContract Arm.abi) := by
  contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, finalizeWide,
    Proof.Sha256.finalizeArm, Proof.Sha256.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Proof.Sha256.Arm.Stream.Finalize.sat, MdStream.Arm.Finalize.sat,
    MdStream.Arm.Finalize.satBase, Impl.Sha256.Arm.Stream.params, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using finalizeSat

theorem finalize :
    Verified Arm.target Impl.Sha256.Arm.Stream.finalize (Spec.Sha256.finalizeContract Arm.abi) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

end VG.Proof.Sha256.Arm.Shared
