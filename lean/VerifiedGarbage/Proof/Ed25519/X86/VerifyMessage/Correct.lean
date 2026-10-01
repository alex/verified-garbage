import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Body
import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Entry

namespace VG.Proof.Ed25519.X86.VerifyMessage
open VG VG.X86 VG.Impl.Ed25519.X86.VerifyMessage

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

theorem body_nosp : NoSp body := by
  have ni : NoSp (.block initArgs) := NoSp.of_all (by decide +kernel)
  have np0 : NoSp (.block (prefixArgs 3 0)) := NoSp.of_all (by decide +kernel)
  have np1 : NoSp (.block (prefixArgs 0 32)) := NoSp.of_all (by decide +kernel)
  have nm : NoSp (.block messageArgs) := NoSp.of_all (by decide +kernel)
  have nf : NoSp (.block finalizeArgs) := NoSp.of_all (by decide +kernel)
  have nr : NoSp (.block reduceArgs) := NoSp.of_all (by decide +kernel)
  have ne : NoSp (.block extendChallenge) := NoSp.of_all (by decide +kernel)
  have nq : NoSp (.block equationArgs) := NoSp.of_all (by decide +kernel)
  exact noSp_seq
    (noSp_seq (noSp_seq ni Whole.init_nosp)
      (noSp_seq (noSp_seq np0 Whole.update_nosp)
      (noSp_seq (noSp_seq np1 Whole.update_nosp)
      (noSp_seq (noSp_seq nm Whole.update_nosp) (noSp_seq nf Whole.finalize_nosp)))))
    (noSp_seq (noSp_seq nr Whole.reduce_nosp)
      (noSp_seq ne (noSp_seq nq equation_nosp)))

theorem verifyMessage_ok {s : State} (h : verifyMessageLocal.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ verifyMessageLocal.post s t := by
  have hL := lay_ok h
  have hb := entry_bounds h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) body_nosp
    (WP.mono (body_ok (push_ctx h) hL (lay_arguments h)) fun u ⟨hu, ho⟩ => ?_)
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · by_cases he : r = .esp
    · subst r
      rw [popped_esp, hu.esp, List.length_replicate]
      exact BitVec.sub_add_cancel _ _
    · rw [popped_gpr _ _ _ he (by intro e; subst r; simp [calleeSaved] at hr), hu.cs r hr he]
  · rw [popped_mem]
    refine hu.frame.readW (r := (lay s).RET) ?_ ?_ (by decide)
    · rw [lay_ret h]; exact Region.contains_self _ _
    · simp only [Lay.outputs, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hL.rc
      · change (lay s).RET.Disjoint (lay s).STK
        rw [lay_ret h, lay_stack h]
        exact (Offset.below_disjoint _ (by decide)).symm
  · change (popped .edx (List.replicate 64 .eax).length u).gpr .eax = _
    rw [popped_gpr _ _ _ (by decide) (by decide)]
    exact ho

end VG.Proof.Ed25519.X86.VerifyMessage
