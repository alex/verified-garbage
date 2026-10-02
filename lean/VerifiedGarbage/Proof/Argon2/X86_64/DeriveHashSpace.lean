import VerifiedGarbage.Proof.Argon2.X86_64.DeriveWords
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveSeparation

/-! Permissions for H₀ follow from the signature and the private ABI frame. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_hash_space {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Initial.Space t := by
  have scratch := private_scratch h prepared
  have member : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  refine ⟨?_, ?_, ?_, private_frame_stack prepared 16 (by decide), ?_,
    by simpa only [BitVec.add_zero] using private_local_write prepared 0 64 (by decide)⟩
  · rw [scratch]; exact private_work_member h prepared
  · rw [scratch]; exact private_stack_disjoint h prepared (abiWork s, true) member 16 (by decide)
  · rw [scratch]; exact private_frame_disjoint h prepared (abiWork s, true) member
  · intro d hd
    have bounds : ∀ d ∈ Initial.slots, d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)

end VG.Proof.Argon2.X86_64.Derive
