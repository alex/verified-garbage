import VerifiedGarbage.Proof.Argon2.X86_64.DeriveRegions

/-! Buffer separation is supplied by the shared signature, including read-only arguments. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure AbiSeparation (s : State) : Prop where
  inputWork : ∀ r ∈ abiInputs s, r.Disjoint (abiWork s)
  matrixWork : (abiMatrix s).Disjoint (abiWork s)
  outputWork : (abiOutput s).Disjoint (abiWork s)
  matrixOutput : (abiMatrix s).Disjoint (abiOutput s)

theorem abi_separation {s : State} (h : AbiEnvironment s) : AbiSeparation s := by
  have pairs := h.pairs
  sig_eval [abiBuffers, abiInputs, abiMatrix, abiWork, abiOutput, abiArguments] at pairs
  sig_split pairs
  constructor
  all_goals sig_eval [abiInputs, abiMatrix, abiWork, abiOutput]
  all_goals sig_and_intros
  all_goals first
    | with_reducible assumption
    | with_reducible exact Region.Disjoint.symm ‹_›

theorem private_scratch {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : t.gpr .rbx = (abiWork s).base := by
  have word := prologue_word h 9 (by decide)
  change (prologueState s).mem.readW ((prologueState s).gpr .rsp + 400) 64 = abiWord s 80 at word
  exact prepared.scratch.trans word

theorem abi_input_lengths {s : State} (h : AbiEnvironment s) : ∀ r ∈ abiInputs s, r.len < 2 ^ 32 := by
  have valid := h.valid
  unfold Spec.Argon2.valid at valid
  obtain ⟨_, _, _, _, _, _, _, _, password, salt, secret, ad⟩ := valid
  sig_eval [abiInputs]
  sig_and_intros
  all_goals with_reducible assumption

end VG.Proof.Argon2.X86_64.Derive
