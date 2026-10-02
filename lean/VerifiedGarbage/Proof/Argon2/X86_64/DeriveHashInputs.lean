import VerifiedGarbage.Proof.Argon2.X86_64.DeriveHashSpace

/-! All four secret inputs keep their original pointers and lengths in the private frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Proof.Argon2.X86_64.Initial (wordAt inputRegion)

theorem private_input_member {s t : State} (words : DeriveWords s t) (input : Nat × Nat)
    (member : input ∈ Initial.inputs) : inputRegion t input.1 input.2 ∈ abiInputs s := by
  simp only [Initial.inputs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · change (⟨wordAt t 104, (wordAt t 96).toNat⟩ : Region) ∈ abiInputs s
    rw [words.password, words.passwordLength]
    exact List.mem_cons_self ..
  · change (⟨wordAt t 88, (wordAt t 80).toNat⟩ : Region) ∈ abiInputs s
    rw [words.salt, words.saltLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  · change (⟨wordAt t 200, (wordAt t 208).toNat⟩ : Region) ∈ abiInputs s
    rw [words.secret, words.secretLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  · change (⟨wordAt t 216, (wordAt t 224).toNat⟩ : Region) ∈ abiInputs s
    rw [words.ad, words.adLength]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem private_hash_inputs {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    ∀ input ∈ Initial.inputs, Initial.InputReady t input.1 input.2 := by
  have words := private_words h prepared
  have space := private_hash_space h prepared
  have separation := abi_separation h
  have scratch := private_scratch h prepared
  intro input hi
  have region := private_input_member words input hi
  have facts : ∀ input ∈ Initial.inputs, input.1 ∈ Initial.slots ∧ input.2 ∈ Initial.slots ∧
      input.1 + 8 ≤ 272 ∧ input.2 + 8 ≤ 272 := by decide
  obtain ⟨pointerSlot, lengthSlot, pointerBound, lengthBound⟩ := facts input hi
  have buffer : (inputRegion t input.1 input.2, false) ∈ abiBuffers s ++ [(abiArguments s, false)] :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, region, rfl⟩))
  refine ⟨space, pointerSlot, lengthSlot, pointerBound, lengthBound,
    abi_input_lengths h _ region, ?_, ?_, ?_⟩
  · intro p n ⟨r, hr, hc⟩
    simp only [List.mem_singleton] at hr; subst r
    refine ⟨_, List.mem_append_left _ ?_, hc⟩
    rw [prepared.rd]
    change inputRegion t input.1 input.2 ∈ (frameStart s Impl.Argon2.X86_64.Derive.saved).rd
    rw [frameStart_rd, h.rd]
    exact List.mem_append_left _ region
  · rw [scratch]; exact separation.inputWork _ region
  · exact (private_stack_disjoint h prepared (inputRegion t input.1 input.2, false) buffer 16 (by decide)).symm

end VG.Proof.Argon2.X86_64.Derive
