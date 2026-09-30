import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Sha512.X86_64.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Md
import VerifiedGarbage.Spec.Sha512.Contract

/-!
# Sha512 on X86_64: the shared contracts

Untrusted: everything here is checked by Lean. The proofs are written against
per-target contracts (`Proof/Sha512/X86_64/Compress.lean`); these theorems move
them to the shared contracts of `Spec/Sha512/Contract.lean`, which the
artifacts are emitted with. `update` and `finalize` hold for any
implementation `f` of the compression function.

The shared contracts give the functions more scratch than these ones use (224
bytes for `compress`, 272 for `update` and `finalize`, sized for the 32-bit
targets): the per-target contracts are first widened to that scratch
(`Verified.widen`, the same code running with the same trace and result),
then moved to the shared ones.
-/

namespace VG.Proof.Sha512.X86_64.Shared

open _root_.VG.X86_64

/-- `compressX86_64` with 224 bytes of scratch. -/
def compressWide : Contract X86_64.isa :=
  { Proof.Sha512.compressX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 64⟩
      let blocks : Region := ⟨s.gpr .rsi, 128 * (s.gpr .rdx).toNat⟩
      let scratch : Region := ⟨s.gpr .rcx, 224⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      s.rd = [blocks] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch }

/-- `updateX86_64` with 272 bytes of scratch. -/
def updateWide : Contract X86_64.isa :=
  { Proof.Sha512.updateX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 192⟩
      let data : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
      let scratch : Region := ⟨s.gpr .r8, 272⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
      s.rd = [data] ∧ s.wr = [state, scratch] ∧
      state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint data ∧ stack.Disjoint scratch }

/-- `finalizeX86_64` with 272 bytes of scratch. -/
def finalizeWide : Contract X86_64.isa :=
  { Proof.Sha512.finalizeX86_64 with
    pre := fun s =>
      let state : Region := ⟨s.gpr .rdi, 192⟩
      let out : Region := ⟨s.gpr .rdx, 64⟩
      let scratch : Region := ⟨s.gpr .rcx, 272⟩
      let ret : Region := ⟨s.gpr .rsp, 8⟩
      let stack : Region := ⟨s.gpr .rsp - 8, 8⟩
      s.rd = [] ∧ s.wr = [state, out, scratch] ∧
      state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
      ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
      stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch }

theorem pfx {a : Addr} {m n : Nat} (h : Nat.ble m n = true) : Region.Prefix ⟨a, m⟩ ⟨a, n⟩ :=
  ⟨rfl, Nat.le_of_ble_eq_true h⟩
theorem sub176 (a : Addr) : Region.Sub ⟨a, 176⟩ ⟨a, 224⟩ := Region.sub_prefix (by decide)
theorem sub224 (a : Addr) : Region.Sub ⟨a, 224⟩ ⟨a, 272⟩ := Region.sub_prefix (by decide)

theorem compressWide_verified (hsat : ∃ s, compressWide.pre s) :
    Verified X86_64.target Impl.Sha512.X86_64.compress compressWide :=
  Verified.widen Proof.Sha512.X86_64.compress_verified
    (fun s => [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 176⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub176 _), h₄, h₅.sub_right (sub176 _), h₆, h₇.sub_right (sub176 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem updateWide_verified {c : Prog X86_64.isa} (hv : Verified X86_64.target c Proof.Sha512.updateX86_64)
    (hsat : ∃ s, updateWide.pre s) : Verified X86_64.target c updateWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .rdi, 192⟩, ⟨s.gpr .r8, 224⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub224 _), h₄, h₅.sub_right (sub224 _), h₆, h₇.sub_right (sub224 _),
        h₈, h₉, h₁₀.sub_right (sub224 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

theorem finalizeWide_verified {c : Prog X86_64.isa} (hv : Verified X86_64.target c Proof.Sha512.finalizeX86_64)
    (hsat : ∃ s, finalizeWide.pre s) : Verified X86_64.target c finalizeWide :=
  Verified.widen hv
    (fun s => [⟨s.gpr .rdi, 192⟩, ⟨s.gpr .rdx, 64⟩, ⟨s.gpr .rcx, 224⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ =>
      ⟨h₁, rfl, h₃, h₄.sub_right (sub224 _), h₅.sub_right (sub224 _), h₆, h₇,
        h₈.sub_right (sub224 _), h₉, h₁₀, h₁₁.sub_right (sub224 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl)
      (.cons (pfx rfl) .nil)))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h) hsat

/-- A state satisfying `compressWide.pre`. -/
def compressSat : State := { Proof.Sha512.X86_64.satState with wr := [⟨0x1000, 64⟩, ⟨0x3000, 224⟩] }

/-- A state satisfying `updateWide.pre`. -/
def updateSat : State :=
  { Proof.Sha512.X86_64.Stream.Update.sat with wr := [⟨0x1000, 192⟩, ⟨0x3000, 272⟩] }

/-- A state satisfying `finalizeWide.pre`. -/
def finalizeSat : State :=
  { Proof.Sha512.X86_64.Stream.Finalize.sat with
    wr := [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 272⟩] }

theorem compress :
    Verified X86_64.target Impl.Sha512.X86_64.compress (Spec.Sha512.compressContract X86_64.abi) := by
  have hi : compressWide.Implies (Spec.Sha512.compressContract X86_64.abi) := by
    sig_implies [Spec.Sha512.compressContract, Spec.Sha512.compressSig, compressWide,
      Proof.Sha512.compressX86_64, X86_64.abi, X86_64.argRegs]
      [compressSat, Proof.Sha512.X86_64.satState] using compressSat
  exact (compressWide_verified hi.sat_left).of_implies hi

theorem init (iv : Spec.Sha512.HashValue) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.init iv) (Spec.Sha512.initContract X86_64.abi iv) :=
  (Proof.Sha512.X86_64.Stream.init_verified iv).of_implies (by
    contract_implies [Spec.Sha512.initContract, Spec.Sha512.initSig, Proof.Sha512.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha512.X86_64.Stream.initSat] using Proof.Sha512.X86_64.Stream.initSat)

theorem updateImplies : updateWide.Implies (Spec.Sha512.updateContract X86_64.abi 8) := by
  sig_implies [Spec.Sha512.updateContract, Spec.Sha512.updateSig, updateWide,
    Proof.Sha512.updateX86_64, X86_64.abi, X86_64.argRegs]
    [updateSat, Proof.Sha512.X86_64.Stream.Update.sat,
      MdStream.X86_64.Update.sat, Impl.Sha512.X86_64.Stream.params] using updateSat

theorem finalizeImplies : finalizeWide.Implies (Spec.Sha512.finalizeContract X86_64.abi 8) := by
  sig_implies [Spec.Sha512.finalizeContract, Spec.Sha512.finalizeSig, finalizeWide,
    Proof.Sha512.finalizeX86_64, X86_64.abi, X86_64.argRegs]
    [finalizeSat, Proof.Sha512.X86_64.Stream.Finalize.sat,
      MdStream.X86_64.Finalize.sat, Impl.Sha512.X86_64.Stream.params] using finalizeSat

open VG.Impl.Sha512.X86_64.Stream (Callee) in
/-- `update`, for any compression function `f` (see `Variant.lean`). -/
theorem update {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.update f) (Spec.Sha512.updateContract X86_64.abi 8) :=
  (updateWide_verified (Proof.Sha512.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha512.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)) updateImplies.sat_left).of_implies updateImplies

open VG.Impl.Sha512.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha512.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha512.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha512.X86_64.Stream (Callee) in
/-- `finalize`, for any compression function `f` (see `Variant.lean`). -/
theorem finalize {f : Callee} (hf : MdStream.X86_64.CalleeOk (P := Stream.params) md f.code)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha512.X86_64.Stream.finalize f)
      (Spec.Sha512.finalizeContract X86_64.abi 8) :=
  (finalizeWide_verified (Proof.Sha512.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha512.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)) finalizeImplies.sat_left).of_implies finalizeImplies

open VG.Impl.Sha512.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha512.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha512.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.all, h, Bool.true_and]
  decide +kernel

end VG.Proof.Sha512.X86_64.Shared
