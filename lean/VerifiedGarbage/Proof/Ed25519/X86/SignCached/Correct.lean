import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Body
import VerifiedGarbage.Proof.Ed25519.X86.SignCached.Entry

namespace VG.Proof.Ed25519.X86.SignCached
open VG VG.X86 VG.Impl.Ed25519.X86.SignCached

private theorem noSp_seq {a b : Prog isa} (ha : NoSp a) (hb : NoSp b) : NoSp (.seq a b) := by
  intro i hi
  rcases List.mem_append.mp hi with hi | hi
  · exact ha i hi
  · exact hb i hi

private theorem noSp_update {args : List Instr} (h : NoSp (.block args)) : NoSp (update args) :=
  noSp_seq h Whole.update_nosp

private theorem noSp_finalize {n : Nat} {b : Bool} (h : NoSp (.block (finalizeArgs n b))) :
    NoSp (finalize n b) := noSp_seq h Whole.finalize_nosp

private theorem noSp_reduce {n : Nat} (h : NoSp (.block (reduceArgs n))) : NoSp (reduce n) :=
  noSp_seq h Whole.reduce_nosp

theorem body_nosp : NoSp body := by
  have ni : NoSp init := noSp_seq (NoSp.of_all (by decide +kernel)) Whole.init_nosp
  have hs : NoSp hashSeed := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_finalize (NoSp.of_all (by decide +kernel))))
  have hn : NoSp hashNonce := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel)))))
  have hc : NoSp hashChallenge := noSp_seq ni (noSp_seq
    (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_update (NoSp.of_all (by decide +kernel)))
      (noSp_finalize (NoSp.of_all (by decide +kernel))))))
  exact noSp_seq (noSp_seq hs (NoSp.of_all (by decide +kernel)))
    (noSp_seq (noSp_seq hn (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) base_nosp)))
    (noSp_seq (noSp_seq hc (noSp_seq (noSp_reduce (NoSp.of_all (by decide +kernel)))
      (noSp_seq (NoSp.of_all (by decide +kernel)) mul_nosp))) (NoSp.of_all (by decide +kernel))))

theorem signCached_ok {s : State} (h : signCachedLocal.pre s) :
    WP isa code s fun t => abiPreserved s t ∧ signCachedLocal.post s t := by
  have hL := lay_ok h
  have hb := entry_bounds h
  refine WP.frame (rs := List.replicate 64 .eax) (by simp) (by simp) (by decide)
    (by simp only [List.length_replicate]; omega) body_nosp
    (WP.mono (body_ok (push_ctx h) hL (lay_arguments h) (entry_key h)) fun u ⟨hu, ho⟩ => ?_)
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
      rintro r (rfl | rfl | rfl)
      · exact hL.ro
      · exact hL.rc
      · change (lay s).RET.Disjoint (lay s).STK
        rw [lay_ret h, lay_stack h]
        exact (Offset.below_disjoint _ (by decide)).symm
  · change Spec.Ed25519.bytesAt (popped .eax (List.replicate 64 .eax).length u).mem
      ((arg s 0).setWidth 64) 64 = _
    rw [popped_mem]
    exact ho

end VG.Proof.Ed25519.X86.SignCached
