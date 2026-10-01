import VerifiedGarbage.Proof.Blake2.X86.LitS
import VerifiedGarbage.Proof.Blake2.X86.CompressS.Compress
import VerifiedGarbage.Proof.Blake2.X86.Stream.Verified
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# BLAKE2s on x86 (32-bit): the instance

Untrusted: everything here is checked by Lean. The compression function's
proof (`CompressS/`) and the generic streaming proofs (`Stream/`) for
BLAKE2s: the constant-time checks, states satisfying the preconditions, and
`Verified` against the shared contracts of `Spec/Blake2/Contract.lean`.
-/

namespace VG.Proof.Blake2.X86.S

open VG VG.X86 VG.Spec.Blake2
open VG.Proof.Blake2 (compressX86 initX86 updateX86 finalizeX86)
open VG.Proof.Blake2.X86.Stream

theorem ok : Ok Spec.Blake2.s := ⟨by decide, .inr rfl⟩

theorem compress_ct : ConstantTime isa (compressX86 s).pre (compressX86 s).pub
    Impl.Blake2.X86.CompressS.compress :=
  VG.Taint.constantTime (A := taint) CompressS.τ₀ (fun _ _ h₁ h₂ hp => CompressS.agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem init_ct : ConstantTime isa (initX86 s).pre (initX86 s).pub (Impl.Blake2.X86.Stream.init s) :=
  VG.Taint.constantTime (A := taint) (τInit 32) (fun _ _ h₁ h₂ hp => init_agree ok h₁ h₂ hp)
    (by taint_decide)

theorem update_ct : ConstantTime isa (updateX86 s).pre (updateX86 s).pub
    (Impl.Blake2.X86.Stream.update 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress) :=
  VG.Taint.constantTime (A := taint) (τUpdate 32) (fun _ _ h₁ h₂ hp => update_agree ok h₁ h₂ hp)
    (by taint_decide)

theorem finalize_ct : ConstantTime isa (finalizeX86 s).pre (finalizeX86 s).pub
    (Impl.Blake2.X86.Stream.finalize 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress) :=
  VG.Taint.constantTime (A := taint) (τFinalize 32) (fun _ _ h₁ h₂ hp => finalize_agree ok h₁ h₂ hp)
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

/-- `compress(0x1000, 0x2000, 0, 0, 0, 0x3000)`. -/
def compressSat : State :=
  satWith (fun a => if a = 0x5005 then 0x10 else if a = 0x5009 then 0x20 else if a = 0x501D then 0x30 else 0)
    [⟨0x2000, 0⟩, ⟨0x5004, 28⟩] [⟨0x1000, 32⟩, ⟨0x3000, 512⟩]

/-- `init(0x1000, 1, 0x2000, 0)`. -/
def initSat : State :=
  satWith (fun a => if a = 0x5005 then 0x10 else if a = 0x5008 then 1 else if a = 0x500D then 0x20 else 0)
    [⟨0x2000, 0⟩, ⟨0x5004, 16⟩] [⟨0x1000, 96⟩]

/-- `update(0x1000, 0, 0x2000, 0, 0x3000)`. -/
def updateSat : State :=
  satWith (fun a => if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5019 then 0x30 else 0)
    [⟨0x2000, 0⟩, ⟨0x5004, 24⟩] [⟨0x1000, 96⟩, ⟨0x3000, 576⟩]

/-- `finalize(0x1000, 0, 0x2000, 0x3000)`. -/
def finalizeSat : State :=
  satWith (fun a => if a = 0x5005 then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5015 then 0x30 else 0)
    [⟨0x5004, 20⟩] [⟨0x1000, 96⟩, ⟨0x2000, 32⟩, ⟨0x3000, 576⟩]

/-! ## The shared contracts -/

theorem compress_implies :
    (Proof.Blake2.compressX86 Spec.Blake2.s).Implies (Spec.Blake2.compressSContract X86.abi) := by
  sig_implies [Spec.Blake2.compressSContract, Spec.Blake2.compressSSig, Proof.Blake2.compressX86,
    Spec.Blake2.blockBytes, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [compressSat, satWith, X86.arg, X86.argAddr, Mem.readW, Mem.read] using compressSat

theorem init_implies : (initX86 Spec.Blake2.s).Implies (Spec.Blake2.initSContract X86.abi) := by
  sig_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, initX86, Proof.Blake2.bufOff,
    Spec.Blake2.blockBytes, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [initSat, satWith, X86.arg, X86.argAddr, Mem.readW, Mem.read] using initSat

theorem update_implies : (updateX86 Spec.Blake2.s).Implies (Spec.Blake2.updateSContract X86.abi 32) := by
  sig_implies [Spec.Blake2.updateSContract, Spec.Blake2.updateSSig, updateX86, Proof.Blake2.countX86,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [updateSat, satWith, X86.arg, X86.argAddr, Mem.readW, Mem.read] using updateSat

theorem finalize_implies : (finalizeX86 Spec.Blake2.s).Implies (Spec.Blake2.finalizeSContract X86.abi 32) := by
  sig_implies [Spec.Blake2.finalizeSContract, Spec.Blake2.finalizeSSig, finalizeX86, Proof.Blake2.countX86,
    Proof.Blake2.bufOff, Spec.Blake2.blockBytes, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [finalizeSat, satWith, X86.arg, X86.argAddr, Mem.readW, Mem.read] using finalizeSat

/-! ## `Verified` -/

/-- The compression function, against the contract the streaming functions call it with. -/
theorem compress_verified_x86 :
    Verified X86.target Impl.Blake2.X86.CompressS.compress (compressX86 Spec.Blake2.s) :=
  ⟨fun s hs => CompressS.correct (CompressS.pre_of s hs), compress_ct, compress_implies.sat_left⟩

theorem callee : CalleeOk Spec.Blake2.s Impl.Blake2.X86.CompressS.compress :=
  CalleeOk.of_verified compress_verified_x86 (NoSp.of_all (by lit_decide)) (by lit_decide)

theorem compress_verified :
    Verified X86.target Impl.Blake2.X86.CompressS.compress (Spec.Blake2.compressSContract X86.abi) :=
  compress_verified_x86.of_implies compress_implies

theorem init_verified :
    Verified X86.target (Impl.Blake2.X86.Stream.init s) (Spec.Blake2.initSContract X86.abi) :=
  (Stream.init_verified ok init_ct init_implies.sat_left).of_implies init_implies

theorem update_verified :
    Verified X86.target
      (Impl.Blake2.X86.Stream.update 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress)
      (Spec.Blake2.updateSContract X86.abi 32) :=
  (Stream.update_verified ok callee update_ct update_implies.sat_left).of_implies update_implies

theorem finalize_verified :
    Verified X86.target
      (Impl.Blake2.X86.Stream.finalize 32 "vg_blake2s_compress" Impl.Blake2.X86.CompressS.compress)
      (Spec.Blake2.finalizeSContract X86.abi 32) :=
  (Stream.finalize_verified ok callee finalize_ct finalize_implies.sat_left).of_implies finalize_implies

end VG.Proof.Blake2.X86.S
