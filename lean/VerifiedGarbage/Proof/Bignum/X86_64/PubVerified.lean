import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# `vg_rsa_public` on x86-64: verified against the shared contract

`pubContract` states the shared contract on the registers and the stack
(`public_implies`); with correctness (`code_correct`) and constant time
(`code_constantTime`), `code` is verified (`public_verified`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public

theorem stackArgs_four (s : State) :
    List.map (stackArg s) (List.range 4) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

/-- A state meeting `pubContract.pre`: a 512-bit modulus, a one-byte
exponent, and the stack arguments at `0x6008`. -/
def satState : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 64 | .r8 => 0x3000 | .r9 => 1
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6009 then 0x40 else if a = 0x6010 then 0x40 else if a = 0x6019 then 0x80
    else if a = 0x6021 then 0x04 else 0
  rd := [⟨0x2000, 64⟩, ⟨0x3000, 1⟩, ⟨0x4000, 64⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x8000, 8192⟩]

/-- The leak of `n` and `e`, as bytes, determines each when `n`'s length is
the same. -/
theorem leak_eq {a b c d : List Byte} (hl : a.length = c.length)
    (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat)) : a = c ∧ b = d := by
  have hi : (a ++ b) = (c ++ d) := List.map_injective_iff.2 (fun _ _ h => BitVec.toNat_inj.1 h) h
  exact List.append_inj hi hl

theorem public_implies : pubContract.Implies (Spec.Rsa.publicContract abi) where
  pre := by
    intro s h
    -- Twice: the stack arguments' list evaluates only on the second pass.
    sig_pre [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, pubContract, stackArgs_four, List.append_eq] at h
    sig_pre [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, pubContract, stackArgs_four, List.append_eq] at h
    sig_split h
    sig_reduce [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, pubContract, stackArgs_four, List.append_eq]
    sig_and_intros
    sig_close
    all_goals with_reducible assumption
  post := by sig_implies_post [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, pubContract, stackArgs_four, List.append_eq]
  pub := by
    rintro s₁ s₂ - - h
    sig_pub [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, pubContract, stackArgs_four, List.append_eq] at h
    simp only [List.getD_cons_succ, List.getD_cons_zero] at h
    obtain ⟨hsp, hl, hdi, hsi, hdx, hcx, h8, h9, a0, a1, a2, a3⟩ := h
    obtain ⟨hn, he⟩ := leak_eq (by simp [Spec.Rsa.bytesAt, hcx]) hl
    refine ⟨?_, a0, a1, a2, a3, hn, he⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hdi, hsi, hdx, hcx, h8, h9, hsp⟩
  sat := by sig_implies_sat [Spec.Rsa.publicContract, Spec.Rsa.publicSig, abi, argRegs, pubContract, stackArgs_four, List.append_eq] [satState, stackArg, stackArgAddr, Mem.readW, Mem.read] using satState

theorem public_verified : Verified target code (Spec.Rsa.publicContract abi) :=
  Verified.of_correct code_correct code_constantTime public_implies

end VG.Proof.Bignum.X86_64
