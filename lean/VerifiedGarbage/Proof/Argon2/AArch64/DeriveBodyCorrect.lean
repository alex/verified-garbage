import VerifiedGarbage.Proof.Argon2.AArch64.DeriveBodyPost

/-! Preparation and the entire algorithm establish the shared API postcondition. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64

def bodyWrites (s : State) : List Region :=
  [abiMatrix s, abiWork s, abiOutput s, ⟨(prologueState s).sp, 272⟩,
    below ((prologueState s).sp) 16]

structure BodyDone (s t : State) : Prop where
  post : (Spec.Argon2.deriveContract AArch64.abi 400).post s t
  sp : t.sp = (prologueState s).sp
  rd : t.rd = (prologueState s).rd
  wr : t.wr = (prologueState s).wr
  frame : Frame (bodyWrites s) (prologueState s).mem t.mem
  unused : ∀ r ∈ [Reg.x25, .x26, .x27, .x28], t.gpr r = s.gpr r

theorem private_body_frame {s t u : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (done : InitialBody.Done t u (abiParams s)) :
    Frame (bodyWrites s) (prologueState s).mem u.mem := by
  have words := private_words h prepared
  have matrix := private_matrix_region h prepared
  have work : (⟨FinalOutput.work t, 16384⟩ : Region) = abiWork s := by
    change (⟨Initial.wordAt t 248, 16384⟩ : Region) = abiWork s
    rw [words.work]; rfl
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  have body := done.frame
  rw [InitFill.writes, matrix, work, output, prepared.sp, prepared.bp] at body
  apply ((private_prepare_frame prepared).mono ?_).trans (body.sub ?_)
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    simp only [bodyWrites, List.mem_cons, true_or, or_true]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨abiMatrix s, by simp [bodyWrites], fun _ h => h⟩
    · exact ⟨abiWork s, by simp [bodyWrites], fun _ h => h⟩
    · exact ⟨abiOutput s, by simp [bodyWrites], fun _ h => h⟩
    · exact ⟨below ((prologueState s).sp) 16, by simp [bodyWrites], fun _ h => h⟩
    · exact ⟨⟨(prologueState s).sp, 272⟩, by simp [bodyWrites], Region.sub_prefix (by decide)⟩

theorem body_ok (v : HPrime.Backend) (name : String) (s : State) (h : AbiEnvironment s) :
    WP isa (Impl.Argon2.AArch64.Derive.body name v.hash) (prologueState s) (BodyDone s) := by
  unfold Impl.Argon2.AArch64.Derive.body
  refine WP.seq ((prologue_prepare s h).mono ?_)
  intro t prepared
  refine (private_pipeline_ok v name s t h prepared).mono ?_
  intro u done
  refine ⟨private_done_post h prepared done, done.sp.trans prepared.sp,
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, private_body_frame h prepared done, ?_⟩
  intro r hr
  have facts : ∀ r ∈ [Reg.x25, .x26, .x27, .x28],
      r ∈ FillCompress.loopRegs ∧ r ≠ .x19 ∧ r ≠ .x24 := by decide
  obtain ⟨member, h19, h24⟩ := facts r hr
  exact (done.unused r hr).trans
    ((prepared.regs r member h19 h24).trans (frameStart_reg s _ r))

end VG.Proof.Argon2.AArch64.Derive
