import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Sha512.X86.Compress
import VerifiedGarbage.Proof.Sha512.X86.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86.Stream.Update
import VerifiedGarbage.Proof.Sha512.X86.Stream.Finalize
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on X86: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/X86/Compress.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with.

The shared contracts give the functions more scratch than these ones use (1328
bytes for `compress`, 1376 for `update` and `finalize`, sized for the x86-64
AVX2 compression function): the per-target contracts are first widened to
that scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones. `update` and `finalize` call the
compression function, using the 20 bytes below the return address.
-/

namespace VG.Proof.Sha512.X86.Shared

open _root_.VG.X86

/-- `compressX86` with 1328 bytes of scratch. -/
def compressWide : Contract X86.isa :=
  { Proof.Sha512.compressX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
      let blocks : Region := ⟨(arg s 1).setWidth 64, 128 * (arg s 2).toNat⟩
      let scratch : Region := ⟨(arg s 3).setWidth 64, 1328⟩
      let args : Region := ⟨argAddr s 0, 16⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
      (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 * (arg s 2).toNat ≤ 2 ^ 32 ∧
      (arg s 3).toNat + 1328 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32 }

/-- `updateX86` with 1376 bytes of scratch. -/
def updateWide : Contract X86.isa :=
  { Proof.Sha512.updateX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 1376⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
      stack.Disjoint data ∧
      (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- `finalizeX86` with 1376 bytes of scratch. -/
def finalizeWide : Contract X86.isa :=
  { Proof.Sha512.finalizeX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
      let out : Region := ⟨(arg s 3).setWidth 64, 64⟩
      let scratch : Region := ⟨(arg s 4).setWidth 64, 1376⟩
      let args : Region := ⟨argAddr s 0, 20⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
      (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
      (arg s 4).toNat + 1376 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32 }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub224 (a : Addr) : Region.Sub ⟨a, 224⟩ ⟨a, 1328⟩ := Region.sub_prefix (by decide)
theorem sub272 (a : Addr) : Region.Sub ⟨a, 272⟩ ⟨a, 1376⟩ := Region.sub_prefix (by decide)
theorem le224 {x : Nat} (h : x + 1328 ≤ 2 ^ 32) : x + 224 ≤ 2 ^ 32 := by omega
theorem le272 {x : Nat} (h : x + 1376 ≤ 2 ^ 32) : x + 272 ≤ 2 ^ 32 := by omega

/-- Rewrites the per-target contracts at a narrowed state (`arg` does not
unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Sha512.compressX86, Proof.Sha512.updateX86, Proof.Sha512.finalizeX86,
    Proof.Sha512.countX86, compressWide, updateWide, finalizeWide, VG.X86.arg_withRegions,
    VG.X86.argAddr_withRegions, State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd,
    State.withRegions_wr] $(loc)?)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified X86.target Impl.Sha512.X86.compress compressWide :=
  Verified.widen Proof.Sha512.X86.Compress.compress_verified
    (fun s => [⟨(arg s 0).setWidth 64, 64⟩, ⟨(arg s 3).setWidth 64, 224⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub224 _), h₄, h₅.sub_right (sub224 _), h₆, h₇.sub_right (sub224 _),
        h₈, h₉.sub_right (sub224 _), h₁₀, h₁₁, le224 h₁₂, h₁₃⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified X86.target Impl.Sha512.X86.Stream.update updateWide :=
  Verified.widen Proof.Sha512.X86.Stream.Update.update_verified
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 5).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃.sub_right (sub272 _), h₄, h₅.sub_right (sub272 _), h₆,
        h₇.sub_right (sub272 _), h₈, h₉.sub_right (sub272 _), h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃,
        h₁₄, le272 h₁₅, h₁₆, h₁₇⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

theorem finalizeWide_verified (hsat : ∃ s, finalizeWide.pre s) :
    Verified X86.target Impl.Sha512.X86.Stream.finalize finalizeWide :=
  Verified.widen Proof.Sha512.X86.Stream.Finalize.finalize_verified
    (fun s => [⟨(arg s 0).setWidth 64, 192⟩, ⟨(arg s 3).setWidth 64, 64⟩,
      ⟨(arg s 4).setWidth 64, 272⟩])
    (fun _ h => by
      obtain ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇, h₁₈, h₁₉⟩ := h
      narrow
      exact ⟨h₁, trivial, h₃, h₄.sub_right (sub272 _), h₅.sub_right (sub272 _), h₆, h₇,
        h₈.sub_right (sub272 _), h₉, h₁₀, h₁₁.sub_right (sub272 _), h₁₂, h₁₃, h₁₄.sub_right (sub272 _),
        h₁₅, h₁₆, le272 h₁₇, h₁₈, h₁₉⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]; exact .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State :=
  { Proof.Sha512.X86.Compress.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 1328⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.X86.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 1376⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.X86.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 1376⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha512.compressContract X86.abi) := by
  sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
    Proof.Sha512.compressX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [compressSat, Proof.Sha512.X86.Compress.satState, Proof.Sha512.X86.Compress.satMem, X86.arg,
      X86.argAddr, Mem.readW, Mem.read] using compressSat

theorem compress :
    Verified X86.target Impl.Sha512.X86.compress (Spec.Sha512.compressContract X86.abi) :=
  (compressWide_verified compressWide_implies.sat_left).of_implies compressWide_implies

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86.target (Impl.Sha512.X86.Stream.init iv) (Spec.Sha512.initContract X86.abi iv) :=
  (Proof.Sha512.X86.Stream.init_verified iv).of_implies (by
    sig_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Sha512.X86.Stream.initSat, Proof.Sha512.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW,
      Mem.read] using Proof.Sha512.X86.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha512.updateContract X86.abi 20) := by
  sig_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, updateWide, Proof.Sha512.updateX86,
    Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, Proof.Sha512.X86.Stream.Update.sat, Proof.Sha512.X86.Stream.Update.satMem, X86.arg,
      X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem update :
    Verified X86.target Impl.Sha512.X86.Stream.update (Spec.Sha512.updateContract X86.abi 20) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha512.finalizeContract X86.abi 20) := by
  contract_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, finalizeWide,
    Proof.Sha512.finalizeX86, Proof.Sha512.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finalizeSat, Proof.Sha512.X86.Stream.Finalize.sat, Proof.Sha512.X86.Stream.Finalize.satMem,
      X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeSat

theorem finalize :
    Verified X86.target Impl.Sha512.X86.Stream.finalize (Spec.Sha512.finalizeContract X86.abi 20) :=
  (finalizeWide_verified finalizeWide_implies.sat_left).of_implies finalizeWide_implies

end VG.Proof.Sha512.X86.Shared
