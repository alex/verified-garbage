import VerifiedGarbage.Proof.Ed448.X86_64.Verify.CT
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyVerified

/-!
# Ed448 verification on x86-64: `Verified`

`verify` is verified against `verifyContract X86_64.abi 272`: correctness
including the ABI (`verify_wp`), constant time (`verify_ct`), and a state
satisfying the precondition, with `vg_ed448_verify_equation`'s own proof.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify

/-- A state satisfying the precondition. -/
def verifySat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x3000 | .rcx => 0x3100 | .r9 => 0x3200 | .rsp => 0x80000
    | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x8000A then 0x01 else 0
  rd := [⟨0x1000, 57⟩, ⟨0x3000, 0⟩, ⟨0x3100, 0⟩, ⟨0x3200, 114⟩, ⟨0x80008, 8⟩]
  wr := [⟨0x10000, 8192⟩]

theorem verify_sat : ∃ s, (Spec.Ed448.verifyContract X86_64.abi 272).pre s := by
  sig_implies_sat [Spec.Ed448.verifyContract, Spec.Ed448.verifySig, Spec.Ed448.scratchWords, X86_64.abi,
    X86_64.argRegs, List.range, List.range.loop] [verifySat, stackArg, stackArgAddr, Mem.readW, Mem.read]
    using verifySat

theorem verify_verified : Verified X86_64.target verify (Spec.Ed448.verifyContract X86_64.abi 272) :=
  ⟨fun _ h => let ⟨t, s', he, ha, hq⟩ := verify_wp Proof.Ed448.X86_64.verifyEquation_ok h; ⟨t, s', he, ha, hq⟩,
    verify_ct Proof.Ed448.X86_64.verifyEquation_ok Proof.Ed448.X86_64.verifyEquation_ct, verify_sat⟩

end VG.Proof.Ed448.X86_64.Verify
