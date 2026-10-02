import VerifiedGarbage.Proof.Argon2.X86_64.DeriveBodyReady

/-! Saving registers and copying arguments leave all original input bytes unchanged. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_prepare_frame {s t : State} (prepared : PrivatePrepared (prologueState s) t) :
    Frame [⟨(prologueState s).gpr .rsp, 272⟩] (prologueState s).mem t.mem := by
  apply prepared.frame.sub
  intro region hr
  simp only [privateWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩
  · exact ⟨_, List.mem_singleton_self _, Offset.sub_base _ (by decide)⟩

theorem private_prologue_frame {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : Frame [below (s.gpr .rsp) 320] s.mem t.mem := by
  have prologue := frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  apply prologue.trans
  have preparation := private_prepare_frame prepared
  rw [prologue_sp] at preparation
  exact preparation.sub (by
    intro region hr; simp only [List.mem_singleton] at hr; subst region
    exact ⟨_, List.mem_singleton_self _, Region.sub_prefix (by decide)⟩)

theorem private_input_bytes {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (input : Nat × Nat) (hi : input ∈ Initial.inputs) :
    Initial.inputBytes t input.1 input.2 =
      Spec.Blake2.bytesAt s.mem (Initial.inputRegion t input.1 input.2).base
        (Initial.inputRegion t input.1 input.2).len := by
  have words := private_words h prepared
  have region := private_input_member words input hi
  have buffer : (Initial.inputRegion t input.1 input.2, false) ∈ abiBuffers s ++ [(abiArguments s, false)] :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, region, rfl⟩))
  have disjoint := h.reserved (below (s.gpr .rsp) 344)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (Initial.inputRegion t input.1 input.2, false) buffer
  have length := abi_input_lengths h _ region
  apply Proof.Blake2.bytesAt_congr
  intro i hi'
  apply (private_prologue_frame h prepared).bytes (R := Initial.inputRegion t input.1 input.2)
    _ (by omega) hi'
  intro r hr
  simp only [List.mem_singleton] at hr; subst r
  exact (disjoint.sub_left (below_sub (by decide) (by decide))).symm

end VG.Proof.Argon2.X86_64.Derive
