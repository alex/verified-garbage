import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Blake2.X86.CompressB.Verified
import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# BLAKE2b on x86 (32-bit): the instance

Untrusted: everything here is checked by Lean. The generic streaming
functions (`Proof/Blake2/X86/Stream/`) for BLAKE2b, calling its compression
function (`Proof/Blake2/X86/CompressB/`): their constant time, and their
proofs moved to the shared contracts of `Spec/Blake2/Contract.lean`.
-/

namespace VG.Proof.Blake2.X86.B

open VG VG.X86 VG.Spec.Blake2
open VG.Proof.Blake2 (initX86 updateX86 finalizeX86)
open VG.Proof.Blake2.X86.Stream

theorem ok : Ok Spec.Blake2.b := ⟨by decide, .inl rfl⟩

/-- What the streaming functions need of the compression function. -/
theorem callee : CalleeOk Spec.Blake2.b Impl.Blake2.X86.CompressB.compress :=
  CalleeOk.of_verified Proof.Blake2.X86.CompressB.compress_verified (NoSp.of_all (by lit_decide))
    (by lit_decide)

theorem init_ct : ConstantTime isa (initX86 b).pre (initX86 b).pub (Impl.Blake2.X86.Stream.init b) :=
  VG.Taint.constantTime (A := taint) (τInit 64) (fun _ _ h₁ h₂ hp => init_agree ok h₁ h₂ hp)
    (by taint_decide)

theorem update_ct : ConstantTime isa (updateX86 b).pre (updateX86 b).pub
    (Impl.Blake2.X86.Stream.update 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress) :=
  VG.Taint.constantTime (A := taint) (τUpdate 64) (fun _ _ h₁ h₂ hp => update_agree ok h₁ h₂ hp)
    (by taint_decide)

theorem finalize_ct : ConstantTime isa (finalizeX86 b).pre (finalizeX86 b).pub
    (Impl.Blake2.X86.Stream.finalize 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress) :=
  VG.Taint.constantTime (A := taint) (τFinalize 64) (fun _ _ h₁ h₂ hp => finalize_agree ok h₁ h₂ hp)
    (by taint_decide)

/-! ## States satisfying the preconditions -/

/-- A state whose stack pointer is `0x5000` and whose memory holds `m`. -/
def satWith (m : Mem) (rd wr : List Region) : State where
  gpr r := match r with
    | .esp => 0x5000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := m
  rd := rd
  wr := wr

/-- `init(0x1000, 1, 0x2000, 0)`. -/
def initSat : State :=
  satWith (fun a => if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500D then 0x20 else 0)
    [⟨0x2000, 0⟩, ⟨0x5004, 16⟩] [⟨0x1000, 192⟩]

/-- `update(0x1000, 0, 0x2000, 0, 0x3000)`. -/
def updateSat : State :=
  satWith (fun a => if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else 0)
    [⟨0x2000, 0⟩, ⟨0x5004, 24⟩] [⟨0x1000, 192⟩, ⟨0x3000, 576⟩]

/-- `finalize(0x1000, 0, 0x2000, 0x3000)`. -/
def finalizeSat : State :=
  satWith (fun a => if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5015 then 0x30 else 0)
    [⟨0x5004, 20⟩] [⟨0x1000, 192⟩, ⟨0x2000, 64⟩, ⟨0x3000, 576⟩]

/-! ## The shared contracts -/

theorem init_implies : (initX86 Spec.Blake2.b).Implies (Spec.Blake2.initBContract X86.abi) := by
  sig_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, initX86, Proof.Blake2.bufOff,
    Spec.Blake2.blockBytes, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initSat, satWith, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initSat

theorem update_implies : (updateX86 Spec.Blake2.b).Implies (Spec.Blake2.updateBContract X86.abi 32) := by
  sig_implies [Spec.Blake2.updateBContract, Spec.Blake2.updateBSig, updateX86, Proof.Blake2.countX86,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, satWith, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem finalize_implies :
    (finalizeX86 Spec.Blake2.b).Implies (Spec.Blake2.finalizeBContract X86.abi 32) := by
  sig_implies [Spec.Blake2.finalizeBContract, Spec.Blake2.finalizeBSig, finalizeX86,
    Proof.Blake2.countX86, Proof.Blake2.bufOff, Spec.Blake2.blockBytes, X86.abi, X86.argSlots,
    X86.argVal, X86.argBytes]
    [finalizeSat, satWith, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeSat

/-! ## Results -/

theorem initB_verified :
    Verified X86.target (Impl.Blake2.X86.Stream.init b) (Spec.Blake2.initBContract X86.abi) :=
  (init_verified ok init_ct init_implies.sat_left).of_implies init_implies

theorem updateB_verified :
    Verified X86.target
      (Impl.Blake2.X86.Stream.update 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress)
      (Spec.Blake2.updateBContract X86.abi 32) :=
  (update_verified ok callee update_ct update_implies.sat_left).of_implies update_implies

theorem finalizeB_verified :
    Verified X86.target
      (Impl.Blake2.X86.Stream.finalize 64 "vg_blake2b_compress" Impl.Blake2.X86.CompressB.compress)
      (Spec.Blake2.finalizeBContract X86.abi 32) :=
  (finalize_verified ok callee finalize_ct finalize_implies.sat_left).of_implies finalize_implies

end VG.Proof.Blake2.X86.B
