import VerifiedGarbage.Proof.Bignum.X86_64.PdCT
import VerifiedGarbage.Proof.Bignum.X86_64.PubVerified

/-!
# `vg_rsa_public_precomputed` on x86-64: verified against the shared contract

`pdContract` states the shared contract on the registers and the stack
(`precomputed_implies`); with correctness (`pdCode_correct`) and constant
time (`pdCode_constantTime`), `Precomputed.code` is verified
(`precomputed_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Rsa.X86_64

/-- A state meeting `pdContract.pre`: a 512-bit modulus, a one-byte
exponent, and the stack arguments at `0x6008`. -/
def pdSatState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 16 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x80
    else if a = 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 128⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

/-- The leak of `pre` and `e`, as numbers, determines each when `pre`'s
length is the same. -/
theorem leak_eq2 {a c : List (BitVec 64)} {b d : List Byte} (hl : a.length = c.length)
    (h : a.map (·.toNat) ++ b.map (·.toNat) = c.map (·.toNat) ++ d.map (·.toNat)) : a = c ∧ b = d := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [hl])
  exact ⟨List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h1,
    List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h2⟩

theorem precomputed_implies : pdContract.Implies (Spec.Rsa.publicPrecomputedContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdContract, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hw, he⟩ := leak_eq2 (by simp [Spec.Rsa.wordsAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hw, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicPrecomputedContract, Spec.Rsa.publicPrecomputedSig, abi, argRegs, pdContract, stackArgs_four, List.append_eq] [pdSatState, stackArg, stackArgAddr, Mem.readW, Mem.read] using pdSatState

theorem precomputed_verified : Verified target Precomputed.code (Spec.Rsa.publicPrecomputedContract abi) :=
  Verified.of_correct pdCode_correct pdCode_constantTime precomputed_implies

end VG.Proof.Bignum.X86_64
