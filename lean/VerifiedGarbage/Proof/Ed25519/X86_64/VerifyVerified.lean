import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCT
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
import VerifiedGarbage.Proof.Framework.Contract

/-! Untrusted: the complete verifier satisfies the merged specification and leakage contract. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {fld : Arith} [EdArith fld]
variable {dbl : Prog isa} [EdDouble dbl]

def verifySatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 0x3000 | .rcx => 0x4000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 32⟩, ⟨0x2000, 64⟩, ⟨0x3000, 64⟩]
  wr := [⟨0x4000, 8192⟩]

/-- The code never loads MXCSR: checked by evaluating it, for each `fld` and
`dbl` it is registered with. -/
abbrev NoMxcsr (c : Prog isa) : Prop := c.allInstrs (fun i => !loadsMxcsr i) = true

theorem verify_ok (hmx : NoMxcsr (verifyEquation fld dbl)) (s : State) (hs : verifyLocal.pre s) :
    ∃ t s', Exec isa (verifyEquation fld dbl) s t s' ∧ abiPreserved s s' ∧ verifyLocal.post s s' := by
  obtain ⟨t, s', he, h⟩ := verify_correct (fld := fld) (dbl := dbl) hs
  exact ⟨t, s', he, abiPreserved_of_exec hmx he h.1, h.2⟩

private theorem byteMap_inj : ∀ {xs ys : List Byte}, xs.map (·.toNat) = ys.map (·.toNat) → xs = ys
  | [], [], _ => rfl
  | a :: xs, b :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, byteMap_inj h.2]

theorem verify_implies : verifyLocal.Implies (Spec.Ed25519.verifyEquationContract X86_64.abi) where
  pre := by
    sig_implies_pre [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs, verifyLocal]
  post s t _ h := by
    sig_post [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs]
    change t.gpr .rax = signWord _ at h
    rw [h]
    generalize Spec.Ed25519.verifyEquation (Spec.Ed25519.bytesAt s.mem (s.gpr .rdi) 32)
      (Spec.Ed25519.bytesAt s.mem (s.gpr .rsi) 64) (Spec.Ed25519.bytesAt s.mem (s.gpr .rdx) 64) = b
    cases b <;> rfl
  pub s t _ _ h := by
    sig_pub [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs] at h
    obtain ⟨sp, bytes, pk, sig, challenge, base⟩ := h
    have hb := byteMap_inj bytes
    obtain ⟨first, last⟩ := List.append_inj' hb (by simp only [bytesAt_length])
    obtain ⟨first, middle⟩ := List.append_inj' first (by simp only [bytesAt_length])
    exact ⟨sp, pk, sig, challenge, base, first, middle, last⟩
  sat := by
    sig_implies_sat [Spec.Ed25519.verifyEquationContract, Spec.Ed25519.verifyEquationSig,
      Spec.Ed25519.scratchWords, X86_64.abi, X86_64.argRegs] [verifySatState] using verifySatState

theorem verify_verified (hmx : NoMxcsr (verifyEquation fld dbl)) :
    Verified X86_64.target (verifyEquation fld dbl) (Spec.Ed25519.verifyEquationContract X86_64.abi) :=
  Verified.of_correct (verify_ok hmx) verify_ct verify_implies

end VG.Proof.Ed25519.X86_64
