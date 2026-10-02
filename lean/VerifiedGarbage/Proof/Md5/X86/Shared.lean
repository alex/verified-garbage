import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86.Inline
import VerifiedGarbage.Proof.Md5.X86.Compress
import VerifiedGarbage.Proof.Md5.X86.Stream.Init
import VerifiedGarbage.Proof.Md5.X86.Stream.Md
import VerifiedGarbage.Spec.Md5.Contract

/-!
# MD5 on x86: the shared contracts

The proofs are written against per-target contracts
(`Proof/Md5/X86/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Md5/Contract.lean`, which the artifacts are emitted with.

The shared contract of `update` lets it write its arguments: the per-target
contract, under which it only reads them, is first widened to writable
arguments (`Verified.narrowTo`, the same code running with the same trace
and result), then moved to the shared one. `update` and `finalize` call the
compression function, using the 20 bytes of stack below the return address.
-/

namespace VG.Proof.Md5.X86.Shared

open _root_.VG.X86

/-- `updateX86` with its arguments writable. -/
def updateWide : Contract X86.isa :=
  { Proof.Md5.updateX86 with
    pre := fun s =>
      let state : Region := ⟨(arg s 0).setWidth 64, 80⟩
      let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
      let scratch : Region := ⟨(arg s 5).setWidth 64, 112⟩
      let args : Region := ⟨argAddr s 0, 24⟩
      let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
      let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
      s.rd = [data] ∧ s.wr = [state, scratch, args] ∧
      state.Disjoint scratch ∧ args.Disjoint state ∧ args.Disjoint scratch ∧
      data.Disjoint state ∧ data.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
      stack.Disjoint data ∧
      (arg s 0).toNat + 80 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
      (arg s 5).toNat + 112 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32 }

/-- Rewrites the per-target contracts at a narrowed state (`arg` does not
unfold cheaply). -/
macro "narrow" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [Proof.Md5.updateX86, updateWide, VG.X86.arg_withRegions, VG.X86.argAddr_withRegions,
    State.withRegions_gpr, State.withRegions_mem, State.withRegions_rd, State.withRegions_wr] $(loc)?)

/-- `update` only reads its arguments. -/
theorem updateWide_verified (hsat : ∃ s, updateWide.pre s) :
    Verified X86.target Impl.Md5.X86.Stream.update updateWide :=
  Verified.narrowTo Proof.Md5.X86.Stream.Update.update_verified
    (fun s => [⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩, ⟨argAddr s 0, 24⟩])
    (fun s => [⟨(arg s 0).setWidth 64, 80⟩, ⟨(arg s 5).setWidth 64, 112⟩])
    (fun _ h => by
      obtain ⟨_, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩ := h
      narrow
      exact ⟨trivial, trivial, h₃, h₆, h₇, h₄, h₅, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅, h₁₆, h₁₇⟩)
    (fun _ h => by
      obtain ⟨h₁, h₂, _⟩ := h
      rw [h₁, h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_singleton_self _))), 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), 0, by simp,
          by simp⟩)
    (fun _ h => by
      obtain ⟨_, h₂, _⟩ := h
      rw [h₂]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, 0, by simp, by simp⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, 0, by simp, by simp⟩)
    (fun _ _ _ h => by narrow at h ⊢; exact h)
    (fun _ _ _ _ h => by narrow; exact h) hsat

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Md5.X86.Stream.Update.sat with
    rd := [⟨0x2000, 0⟩], wr := [⟨0x1000, 80⟩, ⟨0x3000, 112⟩, ⟨0x5004, 24⟩] }

theorem compress :
    Verified X86.target Impl.Md5.X86.compress (Spec.Md5.compressContract X86.abi) :=
  Proof.Md5.X86.compress_verified.of_implies (by
    contract_implies [Spec.Md5.compressContract, Spec.Md5.compressSig, Proof.Md5.compressX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Md5.X86.satState, Proof.Md5.X86.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read]
      using Proof.Md5.X86.satState)

theorem init :
    Verified X86.target Impl.Md5.X86.Stream.init (Spec.Md5.initContract X86.abi) :=
  Proof.Md5.X86.Stream.init_verified.of_implies (by
    contract_implies [Spec.Md5.initContract, Spec.Md5.initSig, Proof.Md5.initX86,
      X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Md5.X86.Stream.initSat, Proof.Md5.X86.Stream.initSatMem, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Md5.X86.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Md5.updateContract X86.abi 20) := by
  contract_implies [Spec.Md5.updateContract, Spec.Md5.updateSig, updateWide,
    Proof.Md5.updateX86, Proof.Md5.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, Proof.Md5.X86.Stream.Update.sat, MdStream.X86.Update.sat, MdStream.X86.Update.sat₀,
      MdStream.X86.Update.satMem, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem update :
    Verified X86.target Impl.Md5.X86.Stream.update (Spec.Md5.updateContract X86.abi 20) :=
  (updateWide_verified updateWide_implies.sat_left).of_implies updateWide_implies

theorem finalize :
    Verified X86.target Impl.Md5.X86.Stream.finalize (Spec.Md5.finalizeContract X86.abi 20) :=
  Proof.Md5.X86.Stream.Finalize.finalize_verified.of_implies (by
    contract_implies [Spec.Md5.finalizeContract, Spec.Md5.finalizeSig,
      Proof.Md5.finalizeX86, Proof.Md5.countX86, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
      [Proof.Md5.X86.Stream.Finalize.sat, MdStream.X86.Finalize.sat, MdStream.X86.Finalize.sat₀,
        MdStream.X86.Finalize.satMem, Impl.Md5.X86.Stream.params, X86.arg, X86.argAddr, Mem.readW,
        Mem.read] using Proof.Md5.X86.Stream.Finalize.sat)

end VG.Proof.Md5.X86.Shared
