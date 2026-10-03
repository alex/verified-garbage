import VerifiedGarbage.Proof.Bignum.X86_64.PcCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-!
# `vg_rsa_public_precompute` on x86-64: verified against the shared contract

`pcContract` states the shared contract on the registers
(`precompute_implies`); with correctness (`pcCode_correct`) and constant
time (`pcCode_constantTime`), `Precompute.code` is verified
(`precompute_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

/-- A state meeting `pcContract.pre`: a 512-bit modulus, `pre` at `0x1000`
and the working space at `0x4000`. -/
def pcSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 16 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x4000 | .r9 => 1024
    | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x2000, 64⟩]
  wr := [⟨0x1000, 128⟩, ⟨0x4000, 8192⟩]

theorem precompute_implies : pcContract.Implies (Spec.Rsa.publicPrecomputeContract abi) where
  pre := by
    intro s h
    sig_pre [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9⟩ := h
    refine ⟨?_, List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) hl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputeContract, Spec.Rsa.publicPrecomputeSig, abi, argRegs, pcContract, List.append_eq] [pcSatState] using pcSatState

theorem precompute_verified : Verified target Precompute.code (Spec.Rsa.publicPrecomputeContract abi) :=
  Verified.of_correct pcCode_correct pcCode_constantTime precompute_implies

end VG.Proof.Bignum.X86_64
