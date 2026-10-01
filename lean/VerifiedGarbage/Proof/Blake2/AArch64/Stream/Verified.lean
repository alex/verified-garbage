import VerifiedGarbage.Proof.Blake2.AArch64.Compress
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.CT
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Init
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Update
import VerifiedGarbage.Proof.Blake2.AArch64.Stream.Finalize
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Blake2.Contract

/-!
# Streaming BLAKE2 on AArch64: `Verified`

Untrusted: everything here is checked by Lean. Correctness (from `Init`,
`Update` and `Finalize`, with the compression function of
`Proof/Blake2/AArch64/Compress.lean`), constant time (from `CT`), and a state
satisfying each precondition, for BLAKE2b and BLAKE2s. `update` and
`finalize` save `x30` in 16 bytes below the stack pointer.
-/

namespace VG.Proof.Blake2.AArch64.Stream

open VG VG.AArch64 VG.Spec.Blake2

theorem calleeB : CalleeOk b (Impl.Blake2.AArch64.compress b) :=
  ⟨Proof.Blake2.AArch64.compressB_correct, Proof.Blake2.AArch64.compressB_noFrames⟩

theorem calleeS : CalleeOk s (Impl.Blake2.AArch64.compress s) :=
  ⟨Proof.Blake2.AArch64.compressS_correct, Proof.Blake2.AArch64.compressS_noFrames⟩

/-! ## States satisfying the preconditions -/

/-- `init` for `w`-bit words, with no key. -/
def initSat (w : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 1 | .x2 => 0x2000 | _ => 0
  sp := 0x4000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩]

/-- `update`, with no data, for `w`-bit words. -/
def updateSat (w : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x4 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := [⟨0x2000, 0⟩]
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x3000, 576⟩]

/-- `finalize`, for `w`-bit words. -/
def finalizeSat (w : Nat) : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x2 => 0x2000 | .x3 => 0x3000 | _ => 0
  sp := 0x5000
  mem _ := 0
  rd := []
  wr := [⟨0x1000, bufOff w + blockBytes w⟩, ⟨0x2000, bufOff w⟩, ⟨0x3000, 576⟩]

/-! ## BLAKE2b -/

theorem initB_correct (st : State) (hs : (initAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.init b) st t s' ∧ abiPreserved st s' ∧
      (initAArch64 b).post st s' :=
  WP.withPreservedV (Init.correct okB hs) (by decide +kernel)

theorem updateB_correct (st : State) (hs : (updateAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update b) st t s' ∧ abiPreserved st s' ∧
      (updateAArch64 b).post st s' :=
  WP.withPreservedV (Update.correct okB calleeB hs) (by decide +kernel)

theorem finalizeB_correct (st : State) (hs : (finalizeAArch64 b).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize b) st t s' ∧ abiPreserved st s' ∧
      (finalizeAArch64 b).post st s' :=
  WP.withPreservedV (Finalize.correct okB calleeB hs) (by decide +kernel)

theorem initB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.init b)
      (Spec.Blake2.initBContract AArch64.abi) :=
  Verified.of_correct initB_correct initB_ct (by
    contract_implies [Spec.Blake2.initBContract, Spec.Blake2.initBSig, Proof.Blake2.initAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs] [initSat]
      using initSat 64)

theorem updateB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update b)
      (Spec.Blake2.updateBContract AArch64.abi 16) :=
  Verified.of_correct updateB_correct updateB_ct (by
    sig_implies [Spec.Blake2.updateBContract, Spec.Blake2.updateBSig, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using updateSat 64)

theorem finalizeB_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize b)
      (Spec.Blake2.finalizeBContract AArch64.abi 16) :=
  Verified.of_correct finalizeB_correct finalizeB_ct (by
    sig_implies [Spec.Blake2.finalizeBContract, Spec.Blake2.finalizeBSig,
      Proof.Blake2.finalizeAArch64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi,
      AArch64.argRegs]
      [finalizeSat] using finalizeSat 64)

/-! ## BLAKE2s -/

theorem initS_correct (st : State) (hs : (initAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.init s) st t s' ∧ abiPreserved st s' ∧
      (initAArch64 s).post st s' :=
  WP.withPreservedV (Init.correct okS hs) (by decide +kernel)

theorem updateS_correct (st : State) (hs : (updateAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.update s) st t s' ∧ abiPreserved st s' ∧
      (updateAArch64 s).post st s' :=
  WP.withPreservedV (Update.correct okS calleeS hs) (by decide +kernel)

theorem finalizeS_correct (st : State) (hs : (finalizeAArch64 s).pre st) :
    ∃ t s', Exec isa (Impl.Blake2.AArch64.Stream.finalize s) st t s' ∧ abiPreserved st s' ∧
      (finalizeAArch64 s).post st s' :=
  WP.withPreservedV (Finalize.correct okS calleeS hs) (by decide +kernel)

theorem initS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.init s)
      (Spec.Blake2.initSContract AArch64.abi) :=
  Verified.of_correct initS_correct initS_ct (by
    contract_implies [Spec.Blake2.initSContract, Spec.Blake2.initSSig, Proof.Blake2.initAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs] [initSat]
      using initSat 32)

theorem updateS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.update s)
      (Spec.Blake2.updateSContract AArch64.abi 16) :=
  Verified.of_correct updateS_correct updateS_ct (by
    sig_implies [Spec.Blake2.updateSContract, Spec.Blake2.updateSSig, Proof.Blake2.updateAArch64,
      Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi, AArch64.argRegs]
      [updateSat] using updateSat 32)

theorem finalizeS_verified :
    Verified AArch64.target (Impl.Blake2.AArch64.Stream.finalize s)
      (Spec.Blake2.finalizeSContract AArch64.abi 16) :=
  Verified.of_correct finalizeS_correct finalizeS_ct (by
    sig_implies [Spec.Blake2.finalizeSContract, Spec.Blake2.finalizeSSig,
      Proof.Blake2.finalizeAArch64, Spec.Blake2.bufOff, Spec.Blake2.blockBytes, AArch64.abi,
      AArch64.argRegs]
      [finalizeSat] using finalizeSat 32)

end VG.Proof.Blake2.AArch64.Stream
