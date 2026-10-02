import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Md
import VerifiedGarbage.Spec.Sha256.Contract
import VerifiedGarbage.Proof.Sha256.X86_64.Stream.Common
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Streaming SHA-256 on x86-64: `init`
-/

namespace VG.Proof.Sha256.X86_64.Stream

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Stream
open VG.Impl.Sha256.X86_64 (at_)
open VG.Proof.Sha256.X86_64 (ea_at contains_offset' writeState stateAt_writeState)

/-! ## `init` -/

variable (iv : Spec.Sha256.HashValue)

theorem initWith_eq : initWith iv = .block [
    .mov32 .rax (.imm iv[0]), .store32 (at_ .rdi (4 * 0)) .rax,
    .mov32 .rax (.imm iv[1]), .store32 (at_ .rdi (4 * 1)) .rax,
    .mov32 .rax (.imm iv[2]), .store32 (at_ .rdi (4 * 2)) .rax,
    .mov32 .rax (.imm iv[3]), .store32 (at_ .rdi (4 * 3)) .rax,
    .mov32 .rax (.imm iv[4]), .store32 (at_ .rdi (4 * 4)) .rax,
    .mov32 .rax (.imm iv[5]), .store32 (at_ .rdi (4 * 5)) .rax,
    .mov32 .rax (.imm iv[6]), .store32 (at_ .rdi (4 * 6)) .rax,
    .mov32 .rax (.imm iv[7]), .store32 (at_ .rdi (4 * 7)) .rax] := rfl

theorem init_post {s₀ : State}
    (hret : Region.Disjoint ⟨s₀.gpr .rsp, 8⟩ ⟨s₀.gpr .rdi, 96⟩) (g : Reg → BitVec 64)
    (hg : ∀ r, r ≠ .rax → g r = s₀.gpr r) :
    gprPreserved s₀ { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) iv } ∧
      (Proof.Sha256.initX86_64 iv).post s₀
        { s₀ with gpr := g, mem := writeState s₀.mem (s₀.gpr .rdi) iv } := by
  have hf : Frame [⟨s₀.gpr .rdi, 96⟩] s₀.mem (writeState s₀.mem (s₀.gpr .rdi) iv) := by
    have c : ∀ k, k < 8 → (⟨s₀.gpr .rdi, 96⟩ : Region).Contains
        (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) (32 / 8) :=
      fun k hk => contains_offset' (by omega) (by omega)
    simp only [writeState]
    refine (((((((((Frame.refl _ _).writeW ?_ _ (c 0 ?_)).writeW ?_ _ (c 1 ?_)).writeW ?_ _
      (c 2 ?_)).writeW ?_ _ (c 3 ?_)).writeW ?_ _ (c 4 ?_)).writeW ?_ _ (c 5 ?_)).writeW ?_ _
      (c 6 ?_)).writeW ?_ _ (c 7 ?_)) <;> simp
  refine ⟨⟨fun r hr => hg r ?_, ?_⟩, Stream.reprFrom_nil (stateAt_writeState _ _ _)⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact hf.readW (Region.contains_self _ _) (by simpa using hret) (by decide)

theorem setWidth_32_64 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x :=
  BitVec.eq_of_toNat_eq (by simp)

set_option simprocs false in
theorem init_correct {s₀ : State} (hp : (Proof.Sha256.initX86_64 iv).pre s₀) :
    WP isa (initWith iv) s₀ fun s' => gprPreserved s₀ s' ∧ (Proof.Sha256.initX86_64 iv).post s₀ s' := by
  obtain ⟨hrd, hwr, hret⟩ := hp
  have o : ∀ k, k < 8 → InRegions s₀.wr (s₀.gpr .rdi + BitVec.ofInt 64 ((4 * k : Nat) : Int)) 4 :=
    fun k hk => ⟨⟨s₀.gpr .rdi, 96⟩, by simp [hwr], contains_offset' (by omega) (by omega)⟩
  have o0 := o 0 (by omega); have o1 := o 1 (by omega); have o2 := o 2 (by omega)
  have o3 := o 3 (by omega); have o4 := o 4 (by omega); have o5 := o 5 (by omega)
  have o6 := o 6 (by omega); have o7 := o 7 (by omega)
  rw [initWith_eq]
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc32, isa, ea_at, State.store32,
    State.setReg32, State.setReg, o0, o1, o2, o3, o4, o5, o6, o7, ite_true, ite_false,
    Option.map_some, Option.some.injEq, exists_eq_left', setWidth_32_64]
  exact init_post iv hret _ fun r hr => by simp [hr]

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 96⟩]

/-- `initWith iv` is verified, given the checks that evaluate its code
(which the kernel can only run on a literal `iv`): it never loads MXCSR, and
the taint analysis accepts it. -/
theorem initWith_verified (hm : (initWith iv).allInstrs (fun i => !loadsMxcsr i) = true)
    {hc} (hct : (taint.check (Taint.ofRegs [.rdi]) (initWith iv) hc).isSome = true) :
    Verified X86_64.target (initWith iv) (Proof.Sha256.initX86_64 iv) := by
  refine ⟨fun s hs => ?_, ?_, ⟨initSat, rfl, rfl, ?_⟩⟩
  · obtain ⟨t, s', he, h⟩ := init_correct iv hs
    exact ⟨t, s', he, abiPreserved_of_exec hm he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi]) ?_ hct
    intro s₁ s₂ _ _ h
    exact Taint.agree_ofRegs fun r hr => by simp at hr; subst hr; exact h
  · exact Region.Disjoint.symm (Offset.disjoint_of_le (by decide) (by decide))

theorem init_verified : Verified X86_64.target init (Proof.Sha256.initX86_64 Spec.Sha256.H0) :=
  initWith_verified _ (by decide +kernel) (hct := by taint_decide)

theorem init224_verified : Verified X86_64.target init224 (Proof.Sha256.initX86_64 Spec.Sha256.H0_224) :=
  initWith_verified _ (by decide +kernel) (hct := by taint_decide)

end VG.Proof.Sha256.X86_64.Stream

/-!
# Sha256 on X86_64: the shared contracts

The proofs are written against per-target contracts
(`Proof/Sha256/X86_64/Contract.lean`); these theorems move them to the shared
contracts of `Spec/Sha256/Contract.lean`, which the artifacts are emitted with.
`update` and `finalize` hold for any implementation `f` of the compression
function.
-/

namespace VG.Proof.Sha256.X86_64.Shared

theorem compress :
    Verified X86_64.target Impl.Sha256.X86_64.compress (Spec.Sha256.compressContract X86_64.abi) :=
  Proof.Sha256.X86_64.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig,
      Proof.Sha256.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.satState] using Proof.Sha256.X86_64.satState)

theorem compress_shani :
    Verified X86_64.target Impl.Sha256.X86_64.ShaNi.compress (Spec.Sha256.compressContract X86_64.abi) :=
  Proof.Sha256.X86_64.ShaNi.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig,
      Proof.Sha256.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.satState] using Proof.Sha256.X86_64.satState)

theorem compress_avx2 :
    Verified X86_64.target Impl.Sha256.X86_64.Avx2.compress (Spec.Sha256.compressContract X86_64.abi) :=
  Proof.Sha256.X86_64.Avx2.compress_verified.of_implies (by
    contract_implies [Spec.Sha256.compressContract, Spec.Sha256.compressSig,
      Proof.Sha256.compressX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.satState] using Proof.Sha256.X86_64.satState)

theorem init :
    Verified X86_64.target Impl.Sha256.X86_64.Stream.init (Spec.Sha256.initContract X86_64.abi) :=
  Proof.Sha256.X86_64.Stream.init_verified.of_implies (by
    contract_implies [Spec.Sha256.initContract, Spec.Sha256.initSig, Proof.Sha256.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.initSat] using Proof.Sha256.X86_64.Stream.initSat)

theorem init224 :
    Verified X86_64.target Impl.Sha256.X86_64.Stream.init224 (Spec.Sha256.init224Contract X86_64.abi) :=
  Proof.Sha256.X86_64.Stream.init224_verified.of_implies (by
    contract_implies [Spec.Sha256.init224Contract, Spec.Sha256.initSig, Proof.Sha256.initX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.initSat] using Proof.Sha256.X86_64.Stream.initSat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `update`, for any compression function `f` (see `Variant.lean`). -/
theorem update {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.update f) (Spec.Sha256.updateContract X86_64.abi 8) :=
  (Proof.Sha256.X86_64.Stream.Update.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
      Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm,
      Bool.true_and]
    decide +kernel)).of_implies (by
    contract_implies [Spec.Sha256.updateContract, Spec.Sha256.updateSig, Proof.Sha256.updateX86_64,
      X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.Update.sat,
        MdStream.X86_64.Update.sat, Impl.Sha256.X86_64.Stream.params] using Proof.Sha256.X86_64.Stream.Update.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem update_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.update f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.update, Impl.MdStream.X86_64.update, Impl.MdStream.X86_64.updateBody,
    Impl.MdStream.X86_64.updateTail, Impl.MdStream.X86_64.compressN, Impl.MdStream.X86_64.compressWith, Code.all, h,
    Bool.true_and]
  decide +kernel

open VG.Impl.Sha256.X86_64.Stream (Callee) in
/-- `finalize`, for any compression function `f` (see `Variant.lean`). -/
theorem finalize {f : Callee} (hf : f.Ok)
    (hm : f.code.allInstrs (fun i => !X86_64.loadsMxcsr i) = true) :
    Verified X86_64.target (Impl.Sha256.X86_64.Stream.finalize f)
      (Spec.Sha256.finalizeContract X86_64.abi 8) :=
  (Proof.Sha256.X86_64.Stream.Finalize.verified_of hf (by
    simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
      Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
      Code.allInstrs, hm, Bool.true_and]
    decide +kernel)).of_implies (by
    contract_implies [Spec.Sha256.finalizeContract, Spec.Sha256.finalizeSig,
      Proof.Sha256.finalizeX86_64, X86_64.abi, X86_64.argRegs]
      [Proof.Sha256.X86_64.Stream.Finalize.sat,
        MdStream.X86_64.Finalize.sat, Impl.Sha256.X86_64.Stream.params] using Proof.Sha256.X86_64.Stream.Finalize.sat)

open VG.Impl.Sha256.X86_64.Stream (Callee) in
theorem finalize_spSafe {f : Callee} (h : f.code.all (fun i => !X86_64.isa.writesSp i) = true) :
    (Impl.Sha256.X86_64.Stream.finalize f).all (fun i => !X86_64.isa.writesSp i) = true := by
  simp only [Impl.Sha256.X86_64.Stream.finalize, Impl.MdStream.X86_64.finalize,
    Impl.MdStream.X86_64.finalizeBody, Impl.MdStream.X86_64.compressAt, Impl.MdStream.X86_64.compressWith,
    Code.all, h, Bool.true_and]
  decide +kernel

end VG.Proof.Sha256.X86_64.Shared
