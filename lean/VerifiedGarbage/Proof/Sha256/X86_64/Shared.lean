import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Spec.Sha256.Contract

/-!
# Sha256 on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha256/X86_64/Contract.lean`); these theorems move
them to the shared contracts of `Spec/Sha256/Contract.lean`, which the
artifacts are emitted with. `update` and `finalize` hold for any
implementation `f` of the compression function.

The shared contracts give the functions more scratch than these ones use (560
bytes for `compress`, 608 for `update` and `finalize`, sized for the AVX2
compression function): the per-target contracts are first widened to that
scratch (`Verified.widen`, the same code running with the same trace and
result), then moved to the shared ones.
-/

namespace VG.Proof.Sha256.X86_64.Shared

open _root_.VG.X86_64

/-- `compressX86_64` with 560 bytes of scratch. -/
def compressWide : Contract X86_64.isa :=
  { Proof.Sha256.compressX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 32⟩
      let blocks : Region := ⟨s.gpr .rsi, 64 * (s.gpr .rdx).toNat⟩
      let scratch : Region := ⟨s.gpr .rcx, 560⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch }

/-- `updateX86_64` with 608 bytes of scratch. -/
def updateWide : Contract X86_64.isa :=
  { Proof.Sha256.updateX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 96⟩
      let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
      let scratch : Region := ⟨s.gpr .r8, 608⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch }

/-- `finalizeX86_64` with 608 bytes of scratch. -/
def finalizeWide : Contract X86_64.isa :=
  { Proof.Sha256.finalizeX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 96⟩
      let out : Region := ⟨s.gpr .rdx, 32⟩
      let scratch : Region := ⟨s.gpr .rcx, 608⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub112 (a : Addr) : Region.Sub ⟨a, 112⟩ ⟨a, 560⟩ := Region.sub_prefix (by decide)
theorem sub160 (a : Addr) : Region.Sub ⟨a, 160⟩ ⟨a, 608⟩ := Region.sub_prefix (by decide)

/-- Any implementation of `compressX86_64`, with 560 bytes of scratch. -/
theorem compressWide_verified {c : Prog X86_64.isa}
    (h : Verified X86_64.target c Proof.Sha256.compressX86_64) (hsat : ∃ s, compressWide.pre s) :
    Verified X86_64.target c compressWide :=
  Verified.widen h
    (fun s => [⟨s.gpr .rdi, 32⟩, ⟨s.gpr .rcx, 112⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub112 _), h₄, h₅.sub_right (sub112 _), h₆, h₇.sub_right (sub112 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_verified {c : Prog X86_64.isa}
    (h : Verified X86_64.target c Proof.Sha256.updateX86_64) (hsat : ∃ s, updateWide.pre s) :
    Verified X86_64.target c updateWide :=
  Verified.widen h
    (fun s => [⟨s.gpr .rdi, 96⟩, ⟨s.gpr .r8, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub160 _), h₄, h₅.sub_right (sub160 _), h₆, h₇.sub_right (sub160 _),
        h₈, h₉, h₁₀.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_verified {c : Prog X86_64.isa}
    (h : Verified X86_64.target c Proof.Sha256.finalizeX86_64) (hsat : ∃ s, finalizeWide.pre s) :
    Verified X86_64.target c finalizeWide :=
  Verified.widen h
    (fun s => [⟨s.gpr .rdi, 96⟩, ⟨s.gpr .rdx, 32⟩, ⟨s.gpr .rcx, 160⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (sub160 _), h₅.sub_right (sub160 _), h₆, h₇,
        h₈.sub_right (sub160 _), h₉, h₁₀, h₁₁.sub_right (sub160 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha256.X86_64.satState with wr := [⟨0x1000, 32⟩, ⟨0x3000, 560⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha256.X86_64.Stream.Update.sat with wr := [⟨0x1000, 96⟩, ⟨0x3000, 608⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha256.X86_64.Stream.Finalize.sat with wr := [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 608⟩] }

theorem compressWide_implies : compressWide.Implies (Spec.Sha256.compressContract X86_64.abi) := by
  contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig, compressWide,
    Proof.Sha256.compressX86_64, X86_64.abi, X86_64.argRegs]
    [compressSat, Proof.Sha256.X86_64.satState] using compressSat

theorem compress :
    Verified X86_64.target Impl.Sha256.X86_64.compress (Spec.Sha256.compressContract X86_64.abi) :=
  (compressWide_verified Proof.Sha256.X86_64.compress_verified compressWide_implies.sat_left).of_implies
    compressWide_implies

theorem compress_shani :
    Verified X86_64.target Impl.Sha256.X86_64.ShaNi.compress (Spec.Sha256.compressContract X86_64.abi) :=
  (compressWide_verified Proof.Sha256.X86_64.ShaNi.compress_verified
    compressWide_implies.sat_left).of_implies compressWide_implies

theorem init :
    Verified X86_64.target Impl.Sha256.X86_64.Stream.init (Spec.Sha256.initContract X86_64.abi) :=
  Proof.Sha256.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.initSat] using Proof.Sha256.X86_64.Stream.initSat)

theorem updateWide_implies : updateWide.Implies (Spec.Sha256.updateContract X86_64.abi 8) := by
  contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, updateWide,
    Proof.Sha256.updateX86_64, X86_64.abi, X86_64.argRegs]
    [updateSat, Proof.Sha256.X86_64.Stream.Update.sat, MdStream.X86_64.Update.sat,
      Impl.Sha256.X86_64.Stream.params] using updateSat

theorem finalizeWide_implies : finalizeWide.Implies (Spec.Sha256.finalizeContract X86_64.abi 8) := by
  contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig, finalizeWide,
    Proof.Sha256.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [finalizeSat, Proof.Sha256.X86_64.Stream.Finalize.sat, MdStream.X86_64.Finalize.sat,
      Impl.Sha256.X86_64.Stream.params] using finalizeSat

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `update`, for any compression function `f` (see `Variant.lean`). -/
theorem update {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.update f) (Spec.Sha256.updateContract X86_64.abi 8) :=
  (updateWide_verified (Proof.Sha256.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.allInstrs, hm,
      Bool.true_and]
    decide +kernel)) updateWide_implies.sat_left).of_implies updateWide_implies

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressAt, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `finalize`, for any compression function `f` (see `Variant.lean`). -/
theorem finalize {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.finalize f)
      (Spec.Sha256.finalizeContract X86_64.abi 8) :=
  (finalizeWide_verified (Proof.Sha256.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Code.allInstrs, hm, Bool.true_and]
    decide +kernel)) finalizeWide_implies.sat_left).of_implies finalizeWide_implies

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Code.all, h, Bool.true_and]
  decide +kernel

end VG.Proof.Sha256.X86_64.Shared
