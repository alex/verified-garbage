import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyCT
import VerifiedGarbage.Proof.Ed25519.AArch64.VerifyLit
import VerifiedGarbage.Proof.Framework.Contract

/-! The complete verifier satisfies the merged specification and leakage contract. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

def verifySatState : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 0x2000 | .x2 => 0x3000 | .x3 => 0x4000 | _ => 0
  sp := 0x8000
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

theorem verify_ok (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa verifyEquation s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' := verify_correct hs

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract AArch64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs, verifyLocal]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs]
    change t.gpr .x0 = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .x0) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .x1) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .x2) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, AArch64.abi, AArch64.argRegs] [verifySatState] using verifySatState

theorem verify_verified : Verified AArch64.target verifyEquation (Spec.Ed25519.verifyEquationContract AArch64.abi) :=
  Verified.of_correct verify_ok verify_ct verify_implies

end VG.Proof.Ed25519.AArch64
