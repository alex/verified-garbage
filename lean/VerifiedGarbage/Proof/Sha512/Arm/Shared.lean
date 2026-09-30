import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Sha512.Arm.Compress
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Finalize
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Init
import VerifiedGarbage.Proof.Sha512.Arm.Stream.Update
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on Arm: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/Arm/Compress.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.
-/

namespace VG.Proof.Sha512.Arm.Shared

open _root_.VG.Arm

/-- `compressArm` with 1328 bytes of scratch. -/
def compressWide : Contract Arm.isa :=
  { Proof.Sha512.compressArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 64⟩
      let blocks : Region := ⟨State.addr (s.gpr .r1), 128 * (s.gpr .r2).toNat⟩
      let scratch : Region := ⟨State.addr (s.gpr .r3), 1328⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 128 * (s.gpr .r2).toNat ≤ 2 ^ 32 ∧
      (s.gpr .r3).toNat + 1328 ≤ 2 ^ 32 }

/-- `updateArm` with 1376 bytes of scratch. -/
def updateWide : Contract Arm.isa :=
  { Proof.Sha512.updateArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let data : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat⟩
      let scratch : Region := ⟨State.addr (stackArg s 2), 1376⟩
      let args : Region := ⟨stackArgAddr s 0, 12⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 32 ∧
      (stackArg s 2).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 12 ≤ 2 ^ 32 }

/-- `finalizeArm` with 1376 bytes of scratch. -/
def finalizeWide : Contract Arm.isa :=
  { Proof.Sha512.finalizeArm with
    pre := fun s =>
      let state : Region := ⟨State.addr (s.gpr .r0), 192⟩
      let out : Region := ⟨State.addr (stackArg s 0), 64⟩
      let scratch : Region := ⟨State.addr (stackArg s 1), 1376⟩
      let args : Region := ⟨stackArgAddr s 0, 8⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      (s.gpr .r0).toNat + 192 ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 64 ≤ 2 ^ 32 ∧
      (stackArg s 1).toNat + 1376 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub224 (a : Addr) : Region.Sub ⟨a, 224⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)
theorem sub272 (a : Addr) : Region.Sub ⟨a, 272⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)
theorem le224 {x : Nat} (h : x + 1328 ≤ 2 ^ 32) : x + 224 ≤ 2 ^ 32 := by omega
theorem le272 {x : Nat} (h : x + 1376 ≤ 2 ^ 32) : x + 272 ≤ 2 ^ 32 := by omega

/-- Rewrites the per-target contracts at a narrowed state (`stackArg` does
not unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sha512.compressArm, Proof.Sha512.updateArm, Proof.Sha512.finalizeArm,
    Proof.Sha512.countArm, compressWide, updateWide, finalizeWide, VG.Arm.stackArg_withRegions,
    VG.Arm.stackArgAddr_withRegions, State.withRegions_gpr, State.withRegions_sp, State.withRegions_mem,
    State.withRegions_rd, State.withRegions_wr] $(loc)?)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.compress compressWide :=
  Verified.widen Proof.Sha512.Arm.Compress.compress_verified
    (fun s => [⟨State.addr (s.gpr .r0), 64⟩, ⟨State.addr (s.gpr .r3), 224⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub224 _), h₄, h₅.sub_right (sub224 _), h₆, h₇, le224 h₈⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.Stream.update updateWide :=
  Verified.widen Proof.Sha512.Arm.Stream.Update.update_verified
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 2), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub272 _), h₄, h₅.sub_right (sub272 _), h₆,
        h₇.sub_right (sub272 _), h₈, h₉, le272 h₁₀, h₁₁⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.Arm.Stream.Finalize.finalize_verified
    (fun s => [⟨State.addr (s.gpr .r0), 192⟩, ⟨State.addr (stackArg s 0), 64⟩,
      ⟨State.addr (stackArg s 1), 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, le272 h₁₁, h₁₂⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State :=
  { Proof.Sha512.Arm.Compress.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State := { Proof.Sha512.Arm.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.Arm.Stream.Finalize.sat with wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha512.compressContract Arm.abi) := by
  sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
    Proof.Sha512.compressArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [compressSat, Proof.Sha512.Arm.Compress.satState, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using compressSat

theorem compress :
    Verified Arm.target Impl.Sha512.Arm.compress (Spec.Sha512.compressContract Arm.abi) :=
  (compressWide_verified compressWide_implies.sat_left).of_implies compressWide_implies

theorem init (iv : Spec.Sha512.HashValue) :
    Verified Arm.target (Impl.Sha512.Arm.Stream.init iv) (Spec.Sha512.initContract Arm.abi iv) :=
  (Proof.Sha512.Arm.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
      [Proof.Sha512.Arm.Stream.initSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
      Mem.read] using Proof.Sha512.Arm.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha512.updateContract Arm.abi) := by
  sig_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, updateWide, Proof.Sha512.updateArm,
    Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr]
    [updateSat, Proof.Sha512.Arm.Stream.Update.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using updateSat

theorem update :
    Verified Arm.target Impl.Sha512.Arm.Stream.update (Spec.Sha512.updateContract Arm.abi) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha512.finalizeContract Arm.abi) := by
  contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, finalizeWide,
    Proof.Sha512.finalizeArm, Proof.Sha512.countArm, Arm.abi, Arm.argRegs, Arm.reduceClassify,
    Arm.Loc.val, Arm.State.addr]
    [finalizeSat, Proof.Sha512.Arm.Stream.Finalize.sat, Arm.stackArg, Arm.stackArgAddr, Mem.readW,
    Mem.read] using finalizeSat

theorem finalize :
    Verified Arm.target Impl.Sha512.Arm.Stream.finalize (Spec.Sha512.finalizeContract Arm.abi) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

end VG.Proof.Sha512.Arm.Shared
