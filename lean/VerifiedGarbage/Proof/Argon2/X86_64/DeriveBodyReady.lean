import VerifiedGarbage.Proof.Argon2.X86_64.DeriveFinalLayout
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveHeader
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveParameters

/-! The shared API contract supplies the complete body's precondition after preparation. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem DeriveWords.of_state {s a b : State} (h : DeriveWords s a) (k : InitialBody.SameFrame a b) :
    DeriveWords s b :=
  ⟨(k.word 72).trans h.passes, (k.word 80).trans h.saltLength, (k.word 88).trans h.salt,
    (k.word 96).trans h.passwordLength, (k.word 104).trans h.password, (k.word 112).trans h.kind,
    (k.word 176).trans h.memory, (k.word 184).trans h.lanes, (k.word 200).trans h.secret,
    (k.word 208).trans h.secretLength, (k.word 216).trans h.ad, (k.word 224).trans h.adLength,
    (k.word 232).trans h.matrix, (k.word 240).trans h.blocks, (k.word 248).trans h.work,
    (k.word 256).trans h.output, (k.word 264).trans h.tagLength⟩

theorem private_body_ready {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    InitialBody.Ready (abiParams s) (dimensionState t (abiParams s)) := by
  let a := dimensionState t (abiParams s)
  have keeps : InitialBody.SameFrame t a := dimension_frame t (abiParams s)
  have words : DeriveWords s a := (private_words h prepared).of_state keeps
  have matrix : FillKernel.matrix a = FillKernel.matrix t := by
    unfold FillKernel.matrix; rw [keeps.mem, keeps.bp]
  have scratch : a.gpr .rbx = FinalOutput.work a := by
    rw [keeps.bx, private_scratch h prepared]
    exact words.work.symm
  refine ⟨keeps.hashSpace (private_hash_space h prepared),
    fun input hi => keeps.input (private_hash_inputs h prepared input hi), private_header words, ?_⟩
  refine ⟨?_, (private_fill_environment h prepared).of_state keeps.bp keeps.sp keeps.mem keeps.rd keeps.wr,
    keeps.output (private_final_layout h prepared), h.valid.2.2.1, scratch⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, words.lanes, ?_, ?_⟩
  · rw [matrix]
    exact (private_memory_space h prepared).same keeps.wr keeps.bp keeps.bx keeps.sp
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 232 8 (by decide)
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 184 8 (by decide)
  · rw [keeps.rd, keeps.wr, keeps.bp]; exact private_local_read prepared 240 8 (by decide)
  · rfl
  · rw [← Proof.Argon2.blocks_lanes (abiParams s) h.valid.1]; exact words.blocks
  · exact RegUpd.gpr_setReg_self ..

theorem private_pipeline_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s t : State) (h : AbiEnvironment s) (prepared : PrivatePrepared (prologueState s) t) :
    WP isa (.seq Impl.Argon2.X86_64.Parameters.code
      (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v))) t (InitialBody.Done t · (abiParams s)) :=
  parameters_body_ok v name t (abiParams s) (private_parameters h prepared) (private_body_ready h prepared)

end VG.Proof.Argon2.X86_64.Derive
