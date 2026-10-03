import VerifiedGarbage.Proof.Argon2.X86_64.DeriveSpSafe
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveAbi
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveFrame
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveLit
import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Correct
import VerifiedGarbage.Proof.Argon2.X86_64.InitialLit
import VerifiedGarbage.Proof.Argon2.X86_64.MemoryInitLit
import VerifiedGarbage.Proof.Argon2.X86_64.ParametersLit
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveNormalize
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Argon2.X86_64.InitialBodyReviewedState
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveSaved
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Argon2.X86_64.Parameters
import VerifiedGarbage.Proof.Argon2.X86_64.InitialBodyState
import VerifiedGarbage.Proof.Argon2.X86_64.DeriveRegions
import VerifiedGarbage.Proof.Argon2.X86_64.InitialBody

/-! Merged from `Proof.Argon2.X86_64.ParametersCT`. -/
section
/-! Rounded-memory computation has a fixed trace, reading only public frame addresses. -/

namespace VG.Proof.Argon2.X86_64.Parameters

open VG VG.X86_64

theorem code_rel : RelCT isa (fun s t => s.gpr .rbp = t.gpr .rbp)
    Impl.Argon2.X86_64.Parameters.code (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rbp])
    (fun _ _ h => Taint.agree_ofRegs (by
      intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst r; exact h)) (by taint_decide)

end VG.Proof.Argon2.X86_64.Parameters
end

/-! Merged from `Proof.Argon2.X86_64.DeriveWords`. -/
section
/-! Exact words consumed by hashing, initialization, filling, and finalization. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Proof.Argon2.X86_64.Initial (wordAt)

theorem params_variant_code (kind passes memory lanes tagLen : Nat) (bound : kind ≤ 2) :
    (Spec.Argon2.params kind passes memory lanes tagLen).variant.code = kind := by
  by_cases zero : kind = 0
  · subst kind; rfl
  · by_cases one : kind = 1
    · subst kind; rfl
    · have two : kind = 2 := by omega
      subst kind; rfl

structure DeriveWords (s t : State) : Prop where
  passes : wordAt t 72 = BitVec.ofNat 64 (abiParams s).passes
  saltLength : wordAt t 80 = s.gpr .r8
  salt : wordAt t 88 = s.gpr .rcx
  passwordLength : wordAt t 96 = s.gpr .rdx
  password : wordAt t 104 = s.gpr .rsi
  kind : wordAt t 112 = BitVec.ofNat 64 (abiParams s).variant.code
  memory : wordAt t 176 = BitVec.ofNat 64 (abiParams s).memory
  lanes : wordAt t 184 = BitVec.ofNat 64 (abiParams s).lanes
  secret : wordAt t 200 = abiWord s 32
  secretLength : wordAt t 208 = abiWord s 40
  ad : wordAt t 216 = abiWord s 48
  adLength : wordAt t 224 = abiWord s 56
  matrix : wordAt t 232 = abiWord s 64
  blocks : wordAt t 240 = BitVec.ofNat 64 (abiParams s).blocks
  work : wordAt t 248 = abiWord s 80
  output : wordAt t 256 = abiWord s 88
  tagLength : wordAt t 264 = BitVec.ofNat 64 (abiParams s).tagLen

theorem private_words {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : DeriveWords s t := by
  have parameters := private_parameters h prepared
  refine ⟨?_, private_argument_word prepared (80, .r8) (by decide),
    private_argument_word prepared (88, .rcx) (by decide),
    private_argument_word prepared (96, .rdx) (by decide),
    private_argument_word prepared (104, .rsi) (by decide), ?_, parameters.memoryWord, parameters.lanesWord,
    private_stack_word h prepared 3 (by decide), private_stack_word h prepared 4 (by decide),
    private_stack_word h prepared 5 (by decide), private_stack_word h prepared 6 (by decide),
    private_stack_word h prepared 7 (by decide), ?_, private_stack_word h prepared 9 (by decide),
    private_stack_word h prepared 10 (by decide), ?_⟩
  · have word := private_argument_word prepared (72, .r9) (by decide)
    change wordAt t 72 = ((s.gpr .r9).setWidth 32).setWidth 64 at word
    change wordAt t 72 = BitVec.ofNat 64 ((s.gpr .r9).setWidth 32).toNat
    rw [word, BitVec.ofNat_toNat]
  · have code := params_variant_code ((s.gpr .rdi).setWidth 32).toNat
      (abiParams s).passes (abiParams s).memory (abiParams s).lanes (abiParams s).tagLen h.kind
    change (abiParams s).variant.code = ((s.gpr .rdi).setWidth 32).toNat at code
    rw [code]
    have word := private_argument_word prepared (112, .rdi) (by decide)
    change wordAt t 112 = ((s.gpr .rdi).setWidth 32).setWidth 64 at word
    rw [word, BitVec.ofNat_toNat]
  · have word := private_stack_word h prepared 8 (by decide)
    change wordAt t 240 = abiWord s 72 at word
    rw [word, ← h.blocks, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · have word := private_stack_word h prepared 11 (by decide)
    change wordAt t 264 = abiWord s 96 at word
    change wordAt t 264 = BitVec.ofNat 64 (abiWord s 96).toNat
    rw [word, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveSeparation`. -/
section
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
end

/-! Merged from `Proof.Argon2.X86_64.DeriveParameters`. -/
section
/-! Compute the rounded lane length before entering the complete Argon2 body. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64 VG.Spec.Argon2
open VG.Impl.Argon2.X86_64.Initial

/-- A specification state for the body's readiness predicate, not executable code. -/
def dimensionState (s : State) (p : Params) : State :=
  s.setReg .r13 (BitVec.ofNat 64 p.laneLen)

theorem dimension_frame (s : State) (p : Params) : InitialBody.SameFrame s (dimensionState s p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact RegUpd.gpr_setReg_of_ne _ _ (by decide)
  · exact RegUpd.gpr_setReg_of_ne _ _ (by decide)
  · exact RegUpd.gpr_setReg_of_ne _ _ (by decide)
  · exact RegUpd.mem_setReg ..
  · exact RegUpd.rd_setReg ..
  · exact RegUpd.wr_setReg ..

theorem parameters_frame {s t : State} (p : Params)
    (keeps : Divide.Keeps Parameters.changed s t) :
    InitialBody.SameFrame (dimensionState s p) t := by
  have frame := dimension_frame s p
  refine ⟨?_, ?_, ?_, keeps.mem.trans frame.mem.symm,
    keeps.rd.trans frame.rd.symm, keeps.wr.trans frame.wr.symm⟩
  · exact (keeps.regs .rbp (by decide)).trans frame.bp.symm
  · exact (keeps.regs .rbx (by decide)).trans frame.bx.symm
  · exact (keeps.regs .rsp (by decide)).trans frame.sp.symm

theorem parameters_ready {s t : State} {p : Params}
    (h : InitialBody.Ready p (dimensionState s p))
    (length : t.gpr .r13 = BitVec.ofNat 64 p.laneLen)
    (keeps : Divide.Keeps Parameters.changed s t) : InitialBody.Ready p t :=
  h.of_state (parameters_frame p keeps) length

theorem parameters_body_ok (v : Proof.Blake2.X86_64.Backend) (name : String)
    (s : State) (p : Params) (parameters : Parameters.Ready p s)
    (body : InitialBody.Ready p (dimensionState s p)) :
    WP isa (.seq Impl.Argon2.X86_64.Parameters.code
      (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v))) s (InitialBody.Done s · p) := by
  refine WP.seq ((Parameters.code_ok s p parameters).mono ?_)
  rintro a ⟨length, keeps⟩
  refine (InitialBody.code_ok v name a p (parameters_ready body length keeps)).mono ?_
  intro t done
  have bp := keeps.regs .rbp (by decide)
  have sp := keeps.regs .rsp (by decide)
  have base : FillKernel.matrix a = FillKernel.matrix s := by
    unfold FillKernel.matrix; rw [keeps.mem, bp]
  have work : FinalOutput.work a = FinalOutput.work s := by
    unfold FinalOutput.work; rw [keeps.mem, bp]
  have output : FinalOutput.output a = FinalOutput.output s := by
    unfold FinalOutput.output; rw [keeps.mem, bp]
  refine ⟨?_, done.bp.trans bp, done.sp.trans sp,
    done.rd.trans keeps.rd, done.wr.trans keeps.wr, ?_⟩
  · have digest := done.digest
    simp only [Initial.inputBytes, Initial.wordAt, keeps.mem, bp, output] at digest
    exact digest
  · have frame := done.frame
    rw [InitFill.writes_eq s a p bp sp base work output] at frame
    rw [keeps.mem] at frame
    exact frame

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveInputBytes`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveMemorySpace`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveHashSpace`. -/
section
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
end

/-! Merged from `Proof.Argon2.X86_64.DeriveHashInputs`. -/
section
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
end

/-! Merged from `Proof.Argon2.X86_64.DeriveAllocations`. -/
section
/-! The exact matrix and output allocations of the signature remain writable. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_matrix_region {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
  have words := private_words h prepared
  change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
  rw [words.matrix, ← h.blocks]; rfl

theorem private_local_cover {s t : State} (prepared : PrivatePrepared (prologueState s) t)
    (n : Nat) (bound : n ≤ 272) : Covers [⟨t.gpr .rbp, n⟩] t.wr := by
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨⟨t.gpr .rbp, 272⟩, ?_, ?_⟩
  · rw [prepared.wr, prepared.bp]
    exact frameStart_locals s _
  · unfold Region.Contains at hc ⊢
    exact Nat.le_trans hc bound

theorem private_matrix_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩] t.wr := by
  have words := private_words h prepared
  have member : abiMatrix s ∈ t.wr := private_wr_member prepared _ (by rw [h.wr]; exact List.mem_cons_self ..)
  have matrix : (⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s := by
    change (⟨Initial.wordAt t 232, (abiParams s).blocks * 1024⟩ : Region) = abiMatrix s
    rw [words.matrix, ← h.blocks]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiMatrix s, member, matrix ▸ hc⟩

theorem private_output_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    Covers [⟨FinalOutput.output t, (abiParams s).tagLen⟩] t.wr := by
  have words := private_words h prepared
  have member : abiOutput s ∈ t.wr := private_wr_member prepared _ (by
    rw [h.wr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  intro p n ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  exact ⟨abiOutput s, member, output ▸ hc⟩

theorem private_work_cover {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (n : Nat) (bound : n ≤ 16384) :
    Covers [⟨FinalOutput.work t, n⟩] t.wr := by
  have words := private_words h prepared
  intro p k ⟨region, hr, hc⟩
  simp only [List.mem_singleton] at hr; subst region
  refine ⟨abiWork s, private_work_member h prepared, ?_⟩
  change Region.Contains ⟨abiWord s 80, 16384⟩ p k
  have pointer : FinalOutput.work t = abiWord s 80 := words.work
  rw [pointer] at hc
  unfold Region.Contains at hc ⊢
  exact Nat.le_trans hc bound

end VG.Proof.Argon2.X86_64.Derive
end

/-! The signature's rounded block allocation supplies all initialization permissions. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_matrix_bytes {s : State} (h : AbiEnvironment s) :
    1024 * ((abiParams s).lanes * (abiParams s).laneLen) = (abiParams s).blocks * 1024 := by
  rw [← Proof.Argon2.blocks_lanes (abiParams s) h.valid.1, Nat.mul_comm]

theorem private_memory_space {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    MemoryInit.Space t (FillKernel.matrix t)
      (1024 * ((abiParams s).lanes * (abiParams s).laneLen)) := by
  have matrix := private_matrix_region h prepared
  have separation := abi_separation h
  have scratch := private_scratch h prepared
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  rw [private_matrix_bytes h]
  refine ⟨private_matrix_cover h prepared, private_local_cover prepared 72 (by decide), ?_,
    ?_, ?_, ?_, (private_frame_stack prepared 24 (by decide)).symm, ?_, ?_, ?_⟩
  · rw [scratch]; exact private_work_member h prepared
  · rw [matrix]; exact private_frame_disjoint h prepared (abiMatrix s, true) matrixMember
  · rw [scratch]; exact private_frame_disjoint h prepared (abiWork s, true) workMember
  · rw [matrix, scratch]; exact separation.matrixWork
  · rw [matrix]; exact private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 24 (by decide)
  · rw [scratch]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 24 (by decide)
  · have blocks := Proof.Argon2.blocks_le_memory (abiParams s)
    have memoryBound := h.valid.2.2.2.2.2.1
    omega

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveHeader`. -/
section
/-! H₀ hashes the original requested memory cost and the exact reviewed parameters. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_header {s t : State} (words : DeriveWords s t) :
    Initial.headerBytes t = Proof.Argon2.initialHeader (abiParams s) := by
  have headerWords : (List.range 6).map (Initial.headerValue t) =
      [BitVec.ofNat 32 (abiParams s).lanes, BitVec.ofNat 32 (abiParams s).tagLen,
        BitVec.ofNat 32 (abiParams s).memory, BitVec.ofNat 32 (abiParams s).passes,
        19#32, BitVec.ofNat 32 (abiParams s).variant.code] := by
    change [(Initial.wordAt t 184).setWidth 32, (Initial.wordAt t 264).setWidth 32,
      (Initial.wordAt t 176).setWidth 32, (Initial.wordAt t 72).setWidth 32, 19#32,
      (Initial.wordAt t 112).setWidth 32] = _
    rw [words.lanes, words.tagLength, words.memory, words.passes, words.kind]
    simp only [BitVec.setWidth_ofNat_of_le (show 32 ≤ 64 by decide)]
  unfold Initial.headerBytes
  rw [← List.flatMap_map, headerWords]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← List.append_assoc,
    Proof.Argon2.initialHeader, Spec.Argon2.le32]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveFinalLayout`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveFillLayout`. -/
section
/-! One reviewed allocation supplies all filling and address-generation ranges. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_fill_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillKernel.Layout (abiParams s) t := by
  have space := private_memory_space h prepared
  rw [private_matrix_bytes h] at space
  refine ⟨?_, private_local_write prepared 16 8 (by decide), space.matrix,
    private_work_cover h prepared 5120 (by decide), ?_, space.frameMatrix.symm, ?_, ?_,
    private_frame_stack prepared 8 (by decide), ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 16, 184, 232, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · have pointer : t.gpr .rbx = FillKernel.work t := by
      rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
    rw [← pointer]
    exact space.matrixWork.sub_right (Region.sub_prefix (by decide))
  · exact (space.stackMatrix.sub_left (below_sub (by decide) (by decide))).symm
  · have pointer : t.gpr .rbx = FillKernel.work t := by
      rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
    rw [← pointer]
    exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · have pointer : t.gpr .rbx = FillKernel.work t := by
      rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
    rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right
      (Region.sub_prefix (by decide))

theorem private_address_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : AddressCalls.Ready t := by
  have space := private_memory_space h prepared
  have pointer : t.gpr .rbx = AddressCalls.work t := by
    rw [private_scratch h prepared]; exact (private_words h prepared).work.symm
  refine ⟨private_local_read prepared 248 8 (by decide), private_work_cover h prepared 8192 (by decide),
    ?_, private_frame_stack prepared 8 (by decide), ?_⟩
  · rw [← pointer]; exact space.frameWork.sub_right (Region.sub_prefix (by decide))
  · rw [← pointer]
    exact (space.stackWork.sub_left (below_sub (by decide) (by decide))).sub_right (Region.sub_prefix (by decide))

theorem private_fill_environment {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FillSetup.Environment (abiParams s) t := by
  have space := private_memory_space h prepared
  have words := private_words h prepared
  have pointer : t.gpr .rbx = AddressCalls.work t := by
    rw [private_scratch h prepared]; exact words.work.symm
  rw [private_matrix_bytes h] at space
  refine ⟨?_, h.valid.2.2.2.1, private_fill_layout h prepared, private_address_layout h prepared, ?_,
    private_local_write prepared 8 8 (by decide), private_local_write prepared 0 8 (by decide),
    ?_, words.blocks, words.passes, words.kind, words.lanes⟩
  · refine ⟨h.valid.1, Nat.lt_trans h.valid.2.1 (by decide), h.valid.2.2.2.2.1,
      h.valid.2.2.2.2.2.1, by decide, h.valid.1, by decide⟩
  · intro d hd
    have bounds : ∀ d ∈ [0, 8, 72, 112, 240], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · rw [← pointer]; exact space.matrixWork.sub_right (Region.sub_prefix (by decide))

end VG.Proof.Argon2.X86_64.Derive
end

/-! Final lane reduction and H′ use the matrix and disjoint output/scratch allocations. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_final_layout {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) : FinalOutput.Ready (abiParams s) t := by
  have words := private_words h prepared
  have separation := abi_separation h
  have environment := private_fill_environment h prepared
  have parameters := environment.parameters
  have blocks := Proof.Argon2.lastIndex_bounds (abiParams s) parameters.lanesPositive
    parameters.segment_bound.1 0 parameters.lanesPositive
  have minimum : 1024 ≤ (abiParams s).blocks * 1024 := by
    have positive : 1 ≤ (abiParams s).blocks := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right 1024 positive
  have matrix := private_matrix_region h prepared
  have work : FinalOutput.work t = (abiWork s).base := words.work
  have output : (⟨FinalOutput.output t, (abiParams s).tagLen⟩ : Region) = abiOutput s := by
    change (⟨Initial.wordAt t 256, (abiParams s).tagLen⟩ : Region) = abiOutput s
    rw [words.output]; rfl
  have matrixMember : (abiMatrix s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have workMember : (abiWork s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have outputMember : (abiOutput s, true) ∈ abiBuffers s ++ [(abiArguments s, false)] := by
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  have matrixWork : (⟨ReductionState.matrix t, 1024⟩ : Region).Disjoint ⟨FinalOutput.work t, 16384⟩ := by
    rw [work]
    apply Region.Disjoint.sub_left separation.matrixWork
    rw [← matrix]
    exact Region.sub_prefix minimum
  have stackMatrix : (below (t.gpr .rsp) 24).Disjoint ⟨ReductionState.matrix t, 1024⟩ := by
    apply Region.Disjoint.sub_right
      (private_stack_disjoint h prepared (abiMatrix s, true) matrixMember 24 (by decide))
    rw [← matrix]; exact Region.sub_prefix minimum
  refine ⟨by have tag := h.valid.2.2.2.2.2.2.1; omega, h.valid.2.2.2.2.2.2.2.1,
    ?_, words.tagLength, ?_, private_output_cover h prepared, ?_, matrixWork, ?_, stackMatrix, ?_, ?_⟩
  · intro d hd
    have bounds : ∀ d ∈ [232, 256, 264, 248], d + 8 ≤ 272 := by decide
    exact private_local_read prepared d 8 (bounds d hd)
  · intro p n ⟨region, member, contains⟩
    simp only [List.mem_singleton] at member; subst region
    have contained : Region.Contains ⟨FillKernel.matrix t, (abiParams s).blocks * 1024⟩ p n := by
      unfold Region.Contains at contains ⊢; exact Nat.le_trans contains minimum
    obtain ⟨r, hr, hc⟩ := private_matrix_cover h prepared p n ⟨_, List.mem_singleton_self _, contained⟩
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  · rw [work]; exact private_work_member h prepared
  · rw [output, work]; exact separation.outputWork
  · rw [output]; exact private_stack_disjoint h prepared (abiOutput s, true) outputMember 24 (by decide)
  · rw [work]; exact private_stack_disjoint h prepared (abiWork s, true) workMember 24 (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveBodyReady`. -/
section
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
end

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
end

/-! Merged from `Proof.Argon2.X86_64.DeriveReturn`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveRestore`. -/
section
/-! Reload all saved registers from their unchanged stack slots. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frameEnd_sp (s : State) (rs : List Reg) :
    (frameEnd s rs).gpr .rsp = s.gpr .rsp + BitVec.ofNat 64 (272 + 8 * rs.length) := by
  induction rs with
  | nil => rw [frameEnd, popped_rsp]; rfl
  | cons r rs ih =>
    rw [frameEnd, popped_rsp, ih, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    exact congrArg (fun n => s.gpr .rsp + BitVec.ofNat 64 n)
      (by simp only [List.length_cons]; omega)

theorem popped_one_reg (s : State) (r : Reg) (notSp : r ≠ .rsp) :
    (popped r 1 s).gpr r = s.mem.readW (s.gpr .rsp) 64 := by
  change ((s.setReg r (s.mem.readW (s.gpr .rsp) 64)).setReg .rsp (s.gpr .rsp + 8)).gpr r = _
  rw [RegUpd.gpr_setReg_of_ne _ _ notSp, RegUpd.gpr_setReg_self]

theorem frameEnd_restore (s : State) (rs : List Reg) (values : Reg → Addr)
    (notSp : .rsp ∉ rs) (distinct : rs.Nodup)
    (words : ∀ j (hj : j < rs.length),
      s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (272 + 8 * rs.length - 8 * (j + 1))) 64 = values rs[j]) :
    ∀ r ∈ rs, (frameEnd s rs).gpr r = values r := by
  induction rs with
  | nil => intro r hr; exact False.elim (List.not_mem_nil hr)
  | cons r rs ih =>
    simp only [List.mem_cons, not_or] at notSp
    have nodup := List.nodup_cons.mp distinct
    have innerWords : ∀ j (hj : j < rs.length),
        s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 (272 + 8 * rs.length - 8 * (j + 1))) 64 = values rs[j] := by
      intro j hj
      have word := words (j + 1) (by simp only [List.length_cons]; omega)
      have offset : 272 + 8 * (r :: rs).length - 8 * (j + 1 + 1) =
          272 + 8 * rs.length - 8 * (j + 1) := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    have inner := ih notSp.2 nodup.2 innerWords
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · rw [frameEnd, popped_one_reg _ _ (Ne.symm notSp.1), frameEnd_mem, frameEnd_sp]
      have word := words 0 (by simp)
      have offset : 272 + 8 * (x :: rs).length - 8 * (0 + 1) = 272 + 8 * rs.length := by
        simp only [List.length_cons]; omega
      rw [offset] at word
      exact word
    · rw [frameEnd, popped_gpr r 1 (frameEnd s rs) (r' := x) (fun h => notSp.2 (h ▸ hx))
        (fun h => nodup.1 (h ▸ hx))]
      exact inner x hx

theorem frame_restored (s t : State) (rs : List Reg) (notSp : .rsp ∉ rs)
    (distinct : rs.Nodup) (space : 272 + 8 * rs.length ≤ (s.gpr .rsp).toNat)
    (sp : t.gpr .rsp = (frameStart s rs).gpr .rsp)
    (unchanged : ∀ j (_hj : j < rs.length),
      t.mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
        (frameStart s rs).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64) :
    ∀ r ∈ rs, (frameEnd t rs).gpr r = s.gpr r := by
  apply frameEnd_restore t rs s.gpr notSp distinct
  intro j hj
  have offsetBound : 8 * (j + 1) ≤ 272 + 8 * rs.length := by omega
  rw [sp, frameStart_sp, ← Offset.ofNat_sub_ofNat offsetBound, Offset.sub_add_sub_cancel,
    unchanged j hj]
  exact frameStart_word s rs notSp space j hj

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveBodySaved`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveBodyPost`. -/
section
/-! The complete body's digest is the public API postcondition on original input memory. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem private_done_post {s t u : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) (done : InitialBody.Done t u (abiParams s)) :
    (Spec.Argon2.deriveContract X86_64.abi 344).post s u := by
  have words := private_words h prepared
  have password := private_input_bytes h prepared (104, 96) (by decide)
  have salt := private_input_bytes h prepared (88, 80) (by decide)
  have secret := private_input_bytes h prepared (200, 208) (by decide)
  have ad := private_input_bytes h prepared (216, 224) (by decide)
  change Initial.inputBytes t 104 96 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 104) (Initial.wordAt t 96).toNat at password
  change Initial.inputBytes t 88 80 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 88) (Initial.wordAt t 80).toNat at salt
  change Initial.inputBytes t 200 208 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 200) (Initial.wordAt t 208).toNat at secret
  change Initial.inputBytes t 216 224 =
    Spec.Blake2.bytesAt s.mem (Initial.wordAt t 216) (Initial.wordAt t 224).toNat at ad
  rw [words.password, words.passwordLength] at password
  rw [words.salt, words.saltLength] at salt
  rw [words.secret, words.secretLength] at secret
  rw [words.ad, words.adLength] at ad
  have digest := done.digest
  change Spec.Blake2.bytesAt u.mem (Initial.wordAt t 256) (abiParams s).tagLen =
    Spec.Argon2.derive (abiParams s) (Initial.inputBytes t 104 96)
      (Initial.inputBytes t 88 80) (Initial.inputBytes t 200 208) (Initial.inputBytes t 216 224) at digest
  rw [words.output, password, salt, secret, ad] at digest
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop]
  exact digest

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveBodyCorrect`. -/
section
/-! Preparation and the entire algorithm establish the shared API postcondition. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def bodyWrites (s : State) : List Region :=
  [abiMatrix s, abiWork s, abiOutput s, ⟨(prologueState s).gpr .rsp, 272⟩,
    below ((prologueState s).gpr .rsp) 24]

structure BodyDone (s t : State) : Prop where
  post : (Spec.Argon2.deriveContract X86_64.abi 344).post s t
  sp : t.gpr .rsp = (prologueState s).gpr .rsp
  rd : t.rd = (prologueState s).rd
  wr : t.wr = (prologueState s).wr
  frame : Frame (bodyWrites s) (prologueState s).mem t.mem

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
    · exact ⟨below ((prologueState s).gpr .rsp) 24, by simp [bodyWrites], fun _ h => h⟩
    · exact ⟨⟨(prologueState s).gpr .rsp, 272⟩, by simp [bodyWrites], Region.sub_prefix (by decide)⟩

theorem body_ok (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State) (h : AbiEnvironment s) :
    WP isa (Impl.Argon2.X86_64.Derive.body name (HPrime.hash v)) (prologueState s) (BodyDone s) := by
  unfold Impl.Argon2.X86_64.Derive.body
  refine WP.seq ((prologue_prepare s h).mono ?_)
  intro t prepared
  refine (private_pipeline_ok v name s t h prepared).mono ?_
  intro u done
  exact ⟨private_done_post h prepared done, done.sp.trans prepared.sp,
    done.rd.trans prepared.rd, done.wr.trans prepared.wr, private_body_frame h prepared done⟩

end VG.Proof.Argon2.X86_64.Derive
end

/-! The whole body leaves the prologue's six saved-register slots untouched. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def savedSlot (s : State) (j : Nat) : Region :=
  ⟨s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1)), 8⟩

theorem saved_slot_sub (s : State) (j : Nat) (bound : j < 6) :
    Region.Sub (savedSlot s j) (below (s.gpr .rsp) 344) :=
  Offset.sub_below _ (by omega) (by omega)

theorem saved_slot_address (s : State) (j : Nat) (bound : j < 6) :
    (savedSlot s j).base = (prologueState s).gpr .rsp + BitVec.ofNat 64 (320 - 8 * (j + 1)) := by
  rw [prologue_sp]
  exact Offset.sub_ofNat_eq _ (by omega)

theorem saved_slot_buffers {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 6)
    (buffer : Region × Bool) (member : buffer ∈ abiBuffers s ++ [(abiArguments s, false)]) :
    (savedSlot s j).Disjoint buffer.1 :=
  (h.reserved _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)) buffer member).sub_left
    (saved_slot_sub s j bound)

theorem saved_slot_writes {s : State} (h : AbiEnvironment s) (j : Nat) (bound : j < 6) :
    ∀ r ∈ bodyWrites s, (savedSlot s j).Disjoint r := by
  intro r hr
  simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · apply saved_slot_buffers h j bound (abiMatrix s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply saved_slot_buffers h j bound (abiWork s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · apply saved_slot_buffers h j bound (abiOutput s, true)
    simp only [abiBuffers, List.mem_append, List.mem_cons, true_or, or_true]
  · change (⟨(savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [saved_slot_address s j bound]
    exact Offset.disjoint_base _ (by omega) (by omega)
  · change (⟨(savedSlot s j).base, 8⟩ : Region).Disjoint _
    rw [saved_slot_address s j bound]
    exact Offset.disjoint_below _ (by omega)

theorem BodyDone.saved {s t : State} (h : AbiEnvironment s) (done : BodyDone s t) (j : Nat) (bound : j < 6) :
    t.mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 =
      (prologueState s).mem.readW (s.gpr .rsp - BitVec.ofNat 64 (8 * (j + 1))) 64 :=
  done.frame.readW (r := savedSlot s j) (Region.contains_self _ _) (saved_slot_writes h j bound) (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! The nested ABI frames return the complete result and restore all saved registers. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def wholeWrites (s : State) : List Region := [abiMatrix s, abiWork s, abiOutput s, below (s.gpr .rsp) 344]

theorem BodyDone.whole_frame {s t : State} (h : AbiEnvironment s) (done : BodyDone s t) :
    Frame (wholeWrites s) s.mem t.mem := by
  have prologue := frameStart_frame s Impl.Argon2.X86_64.Derive.saved (by decide) (by
    have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  apply (prologue.sub ?_).trans (done.frame.sub ?_)
  · intro r hr
    simp only [List.mem_singleton] at hr; subst r
    exact ⟨below (s.gpr .rsp) 344, by simp [wholeWrites], below_sub (by decide) (by decide)⟩
  · intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨abiMatrix s, by simp [wholeWrites], fun _ h => h⟩
    · exact ⟨abiWork s, by simp [wholeWrites], fun _ h => h⟩
    · exact ⟨abiOutput s, by simp [wholeWrites], fun _ h => h⟩
    · refine ⟨below (s.gpr .rsp) 344, by simp [wholeWrites], ?_⟩
      rw [prologue_sp]
      exact Offset.sub_below _ (by decide) (by decide)
    · refine ⟨below (s.gpr .rsp) 344, by simp [wholeWrites], ?_⟩
      rw [prologue_sp]
      unfold below
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
      exact Region.sub_prefix (by decide)

theorem return_post {s t : State} (done : BodyDone s t) :
    (Spec.Argon2.deriveContract X86_64.abi 344).post s (frameEnd t Impl.Argon2.X86_64.Derive.saved) := by
  have post := done.post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at post
  sig_post [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop]
  exact post

theorem code_wp (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    WP isa (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) s fun t =>
      (Spec.Argon2.deriveContract X86_64.abi 344).post s t ∧
      (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧ Frame (wholeWrites s) s.mem t.mem := by
  have h := abi_environment s pre
  unfold Impl.Argon2.X86_64.Derive.code
  apply frame_ok s Impl.Argon2.X86_64.Derive.saved _ _ (by decide)
    (by have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega)
  refine (body_ok v name s h).mono ?_
  intro t done
  refine ⟨done.sp, done.wr, return_post done, ?_, ?_⟩
  · have restored := frame_restored s t Impl.Argon2.X86_64.Derive.saved (by decide) (by decide)
      (by have space := h.stack; change 320 ≤ (s.gpr .rsp).toNat; omega) done.sp
      (fun j hj => done.saved h j hj)
    have stack := (frameEnd_metadata s t Impl.Argon2.X86_64.Derive.saved done.sp done.wr).1
    intro r hr
    have member : ∀ r ∈ calleeSaved, r = .rsp ∨ r ∈ Impl.Argon2.X86_64.Derive.saved := by decide
    rcases member r hr with rfl | hr
    · exact stack
    · exact restored r hr
  · rw [frameEnd_mem]
    exact done.whole_frame h

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePublic`. -/
section
/-! The public entry-point relation reads u32 arguments at their declared width. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

structure AbiPublic (s t : State) : Prop where
  sp : s.gpr .rsp = t.gpr .rsp
  regs : ∀ r ∈ [.rsi, .rdx, .rcx, .r8], s.gpr r = t.gpr r
  smallRegs : ∀ r ∈ [.rdi, .r9], (s.gpr r).setWidth 32 = (t.gpr r).setWidth 32
  smallWords : ∀ d ∈ [8, 16, 24], (abiWord s d).setWidth 32 = (abiWord t d).setWidth 32
  words : ∀ d ∈ [32, 40, 48, 56, 64, 72, 80, 88, 96], abiWord s d = abiWord t d
  references : Spec.Argon2.references (abiParams s)
      (Spec.Blake2.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
      (Spec.Blake2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 32) (abiWord s 40).toNat)
      (Spec.Blake2.bytesAt s.mem (abiWord s 48) (abiWord s 56).toNat) =
    Spec.Argon2.references (abiParams t)
      (Spec.Blake2.bytesAt t.mem (t.gpr .rsi) (t.gpr .rdx).toNat)
      (Spec.Blake2.bytesAt t.mem (t.gpr .rcx) (t.gpr .r8).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 32) (abiWord t 40).toNat)
      (Spec.Blake2.bytesAt t.mem (abiWord t 48) (abiWord t 56).toNat)

theorem abi_public (s t : State) (h : (Spec.Argon2.deriveContract X86_64.abi 344).pub s t) :
    AbiPublic s t := by
  sig_pub [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop] at h
  sig_split h
  constructor
  all_goals sig_eval [abiWord, abiParams]
  all_goals sig_and_intros
  all_goals sig_close
  all_goals with_reducible assumption

theorem AbiPublic.params {s t : State} (h : AbiPublic s t) : abiParams s = abiParams t := by
  unfold abiParams
  rw [h.smallRegs .rdi (by simp), h.smallRegs .r9 (by simp),
    h.smallWords 8 (by simp), h.smallWords 16 (by simp), h.words 96 (by simp)]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePrivatePublic`. -/
section
/-! Merged from `Proof.Argon2.X86_64.DeriveParametersCT`. -/
section
/-! Parameter calculation followed by the complete body obeys the reviewed leakage. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64 VG.Spec.Argon2

structure ParametersRelated (p : Params) (s t : State) : Prop where
  left : Parameters.Ready p s
  right : Parameters.Ready p t
  body : InitialBody.ReviewedRelated p (dimensionState s p) (dimensionState t p)

theorem parameters_body_rel (v : Proof.Blake2.X86_64.Backend) (name : String) (p : Params) :
    RelCT isa (ParametersRelated p)
      (.seq Impl.Argon2.X86_64.Parameters.code
        (Impl.Argon2.X86_64.InitialBody.code name (HPrime.hash v))) (fun _ _ => True) := by
  have preparation := (Parameters.code_rel.mono (P' := ParametersRelated p)
    (fun s t h => by
      have left := dimension_frame s p
      have right := dimension_frame t p
      exact left.bp.symm.trans (h.body.hashing.bp.trans right.bp))
    (fun _ _ h => h)).wpDep (fun s t h =>
      ⟨Parameters.code_ok s p h.left, Parameters.code_ok t p h.right⟩)
  refine preparation.seq ((InitialBody.reviewed_rel v name p).mono ?_ (fun _ _ h => h))
  rintro a b ⟨_, s, t, h, ⟨length₁, keeps₁⟩, ⟨length₂, keeps₂⟩⟩
  exact h.body.of_state (parameters_frame p keeps₁) (parameters_frame p keeps₂) length₁ length₂

end VG.Proof.Argon2.X86_64.Derive
end

/-! Private argument copies retain exactly the reviewed public relation. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64
open VG.Proof.Argon2.X86_64.Initial (wordAt)

theorem DeriveWords.public_words {s₁ s₂ t₁ t₂ : State} (h : AbiPublic s₁ s₂)
    (left : DeriveWords s₁ t₁) (right : DeriveWords s₂ t₂) :
    ∀ d ∈ Initial.slots, wordAt t₁ d = wordAt t₂ d := by
  intro d hd
  simp only [Initial.slots, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [left.passes, right.passes, h.params]
  · rw [left.saltLength, right.saltLength]; exact h.regs .r8 (by simp)
  · rw [left.salt, right.salt]; exact h.regs .rcx (by simp)
  · rw [left.passwordLength, right.passwordLength]; exact h.regs .rdx (by simp)
  · rw [left.password, right.password]; exact h.regs .rsi (by simp)
  · rw [left.kind, right.kind, h.params]
  · rw [left.memory, right.memory, h.params]
  · rw [left.lanes, right.lanes, h.params]
  · rw [left.secret, right.secret]; exact h.words 32 (by simp)
  · rw [left.secretLength, right.secretLength]; exact h.words 40 (by simp)
  · rw [left.ad, right.ad]; exact h.words 48 (by simp)
  · rw [left.adLength, right.adLength]; exact h.words 56 (by simp)
  · rw [left.tagLength, right.tagLength, h.params]

def abiReferences (s : State) : List Nat := Spec.Argon2.references (abiParams s)
  (Spec.Blake2.bytesAt s.mem (s.gpr .rsi) (s.gpr .rdx).toNat)
  (Spec.Blake2.bytesAt s.mem (s.gpr .rcx) (s.gpr .r8).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 32) (abiWord s 40).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 48) (abiWord s 56).toNat)

theorem private_references {s t : State} (h : AbiEnvironment s)
    (prepared : PrivatePrepared (prologueState s) t) :
    InitialBody.references (abiParams s) t = abiReferences s := by
  have words := private_words h prepared
  have password := private_input_bytes h prepared (104, 96) (by decide)
  have salt := private_input_bytes h prepared (88, 80) (by decide)
  have secret := private_input_bytes h prepared (200, 208) (by decide)
  have ad := private_input_bytes h prepared (216, 224) (by decide)
  simp only [Initial.inputRegion] at password salt secret ad
  rw [words.password, words.passwordLength] at password
  rw [words.salt, words.saltLength] at salt
  rw [words.secret, words.secretLength] at secret
  rw [words.ad, words.adLength] at ad
  unfold InitialBody.references abiReferences
  change Spec.Argon2.references (abiParams s) (Initial.inputBytes t 104 96)
    (Initial.inputBytes t 88 80) (Initial.inputBytes t 200 208) (Initial.inputBytes t 216 224) = _
  rw [password, salt, secret, ad]

theorem private_parameters_related {s₁ s₂ t₁ t₂ : State}
    (left : AbiEnvironment s₁) (right : AbiEnvironment s₂) (h : AbiPublic s₁ s₂)
    (prepared₁ : PrivatePrepared (prologueState s₁) t₁)
    (prepared₂ : PrivatePrepared (prologueState s₂) t₂) :
    ParametersRelated (abiParams s₁) t₁ t₂ := by
  have same := h.params
  have ready₁ := private_body_ready left prepared₁
  have ready₂ := private_body_ready right prepared₂
  rw [← same] at ready₂
  have keeps₁ := dimension_frame t₁ (abiParams s₁)
  have keeps₂ := dimension_frame t₂ (abiParams s₁)
  have words₁ := (private_words left prepared₁).of_state keeps₁
  have words₂ := (private_words right prepared₂).of_state keeps₂
  have sp : t₁.gpr .rsp = t₂.gpr .rsp := by rw [prepared₁.sp, prepared₂.sp, prologue_sp, prologue_sp, h.sp]
  have bp : t₁.gpr .rbp = t₂.gpr .rbp := by rw [prepared₁.bp, prepared₂.bp, prologue_sp, prologue_sp, h.sp]
  have bx : t₁.gpr .rbx = t₂.gpr .rbx := by
    rw [private_scratch left prepared₁, private_scratch right prepared₂]
    exact h.words 80 (by simp)
  refine ⟨private_parameters left prepared₁, same.symm ▸ private_parameters right prepared₂, ?_⟩
  refine ⟨ready₁, ready₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨ready₁.hashSpace, ready₁.inputs⟩,
      ⟨ready₂.hashSpace, ready₂.inputs⟩, ?_, ?_, ?_, ?_⟩
    · rw [keeps₁.bp, keeps₂.bp]; exact bp
    · rw [keeps₁.bx, keeps₂.bx]; exact bx
    · rw [keeps₁.sp, keeps₂.sp]; exact sp
    · exact words₁.public_words h words₂
  · exact words₁.matrix.trans ((h.words 64 (by simp)).trans words₂.matrix.symm)
  · exact words₁.output.trans ((h.words 88 (by simp)).trans words₂.output.symm)
  · exact words₁.work.trans ((h.words 80 (by simp)).trans words₂.work.symm)
  · unfold InitialBody.references
    simp only [keeps₁.inputBytes, keeps₂.inputBytes]
    change InitialBody.references (abiParams s₁) t₁ = InitialBody.references (abiParams s₁) t₂
    rw [private_references left prepared₁, same, private_references right prepared₂]
    exact h.references

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DerivePrepareCT`. -/
section
/-! ABI argument preparation accesses only fixed offsets of the public stack. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem prepare_rel : RelCT isa (fun s t => s.gpr .rsp = t.gpr .rsp)
    Impl.Argon2.X86_64.Derive.prepare (fun _ _ => True) :=
  RelCT.taint (A := taint) (Taint.ofRegs [.rsp]) (fun _ _ h =>
    Taint.agree_ofRegs (by intro r hr; simp only [List.mem_singleton] at hr; subst r; exact h))
    (by taint_decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveMxcsr`. -/
section
/-! The complete derivation preserves MXCSR for every BLAKE2b backend. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

local notation "property" => (fun i => !loadsMxcsr i)

theorem initial_mxcsr (v : Proof.Blake2.X86_64.Backend) :
    (Impl.Argon2.X86_64.Initial.code (HPrime.hash v)).allInstrs property = true := by
  have init : (HPrime.hash v).init.allInstrs property = true := by
    change (Impl.Blake2.X86_64.Stream.init Spec.Blake2.b).allInstrs _ = true
    lit_decide
  have update : (HPrime.hash v).update.allInstrs property = true := v.updateMxcsr
  have finalize : (HPrime.hash v).finalize.allInstrs property = true := v.finalizeMxcsr
  simp only [Impl.Argon2.X86_64.Initial.code, Impl.Argon2.X86_64.Initial.start,
    Impl.Argon2.X86_64.Initial.absorb, Impl.Argon2.X86_64.Initial.finish,
    Impl.Argon2.X86_64.HPrime.init, Impl.Argon2.X86_64.HPrime.absorbFixed,
    Impl.Argon2.X86_64.HPrime.update, Impl.Argon2.X86_64.HPrime.finalize, Code.allInstrs]
  rw [init, update, finalize]
  lit_decide

theorem memory_mxcsr (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.MemoryInit.code name (HPrime.hash v)).allInstrs property = true := by
  simp only [Impl.Argon2.X86_64.MemoryInit.code, Impl.Argon2.X86_64.MemoryInit.clear,
    Impl.Argon2.X86_64.MemoryInit.lane, Impl.Argon2.X86_64.MemoryInit.block, Code.allInstrs]
  rw [HPrime.code_mxcsr v]
  lit_decide

theorem frame_mxcsr (body : Prog isa) (rs : List Reg) (h : body.allInstrs property = true) :
    (Impl.Argon2.X86_64.Derive.frame body rs).allInstrs property = true := by
  induction rs with
  | nil => simpa [Impl.Argon2.X86_64.Derive.frame, Code.allInstrs, loadsMxcsr] using h
  | cons r rs ih => simpa [Impl.Argon2.X86_64.Derive.frame, Code.allInstrs, loadsMxcsr] using ih

theorem code_mxcsr (v : Proof.Blake2.X86_64.Backend) (name : String) :
    (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)).allInstrs property = true := by
  unfold Impl.Argon2.X86_64.Derive.code
  apply frame_mxcsr
  simp only [Impl.Argon2.X86_64.Derive.body, Impl.Argon2.X86_64.InitialBody.code,
    Impl.Argon2.X86_64.InitFill.code, Impl.Argon2.X86_64.FillFinish.code,
    Impl.Argon2.X86_64.Finish.code, Impl.Argon2.X86_64.FinalOutput.code, Code.allInstrs]
  rw [initial_mxcsr v, memory_mxcsr v name, HPrime.code_mxcsr v]
  lit_decide

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveFrameCT`. -/
section
/-! Saving and restoring the ABI frame leaks only the public stack pointer. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem frame_rel (rs : List Reg) (body : Prog isa) (P : State → State → Prop)
    (sp : ∀ s t, P s t → s.gpr .rsp = t.gpr .rsp)
    (run : RelCT isa (fun a b => ∃ s t, P s t ∧ a = frameStart s rs ∧ b = frameStart t rs)
      body (fun _ _ => True)) :
    RelCT isa P (Impl.Argon2.X86_64.Derive.frame body rs) (fun _ _ => True) := by
  induction rs generalizing P with
  | nil => exact RelCT.frame sp run
  | cons r rs ih =>
    apply RelCT.frame sp
    apply ih (fun a b => ∃ s t, P s t ∧ a = pushed [r] s ∧ b = pushed [r] t) ?_ ?_
    · rintro a b ⟨s, t, hp, rfl, rfl⟩
      rw [pushed_rsp, pushed_rsp, sp s t hp]
    · apply run.mono ?_ (fun _ _ h => h)
      rintro a b ⟨u, v, ⟨s, t, hp, rfl, rfl⟩, rfl, rfl⟩
      exact ⟨s, t, hp, rfl, rfl⟩

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveCorrect`. -/
section
/-! Functional correctness, termination, memory safety, and the complete System V ABI. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem code_correct (v : Proof.Blake2.X86_64.Backend) (name : String) (s : State)
    (pre : (Spec.Argon2.deriveContract X86_64.abi 344).pre s) :
    ∃ tr t, Exec isa (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) s tr t ∧
      abiPreserved s t ∧ (Spec.Argon2.deriveContract X86_64.abi 344).post s t := by
  obtain ⟨tr, t, run, post, regs, frame⟩ := code_wp v name s pre
  refine ⟨tr, t, run, abiPreserved_of_exec (code_mxcsr v name) run ⟨regs, ?_⟩, post⟩
  have h := abi_environment s pre
  apply frame.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) ?_ (by decide)
  intro r hr
  simp only [wholeWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact h.reserved _ (by simp) (abiMatrix s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact h.reserved _ (by simp) (abiWork s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact h.reserved _ (by simp) (abiOutput s, true)
      (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  · exact Offset.base_disjoint_below _ (by decide)

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveContract`. -/
section
/-! A concrete caller establishes satisfiability of the shared derivation contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def satArgs : List Nat := [8, 1, 1, 0, 0, 0, 0, 0x10000, 8, 0x20000, 0x30000, 4]

def satMem (a : Addr) : Byte :=
  let d := a.toNat - 0x40008
  if 0x40008 ≤ a.toNat ∧ a.toNat < 0x40068 then
    ((BitVec.ofNat 64 (satArgs[d / 8]?.getD 0)) >>> (8 * (d % 8))).setWidth 8
  else 0

def satState : State where
  gpr r := match r with
    | .rsp => 0x40000 | .r9 => 1 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := satMem
  rd := [⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0x40008, 96⟩]
  wr := [⟨0x10000, 8192⟩, ⟨0x20000, 16384⟩, ⟨0x30000, 4⟩]

theorem contract_sat : ∃ s, (Spec.Argon2.deriveContract X86_64.abi 344).pre s := by
  refine ⟨satState, ?_⟩
  sig_sat_check [Spec.Argon2.deriveContract, Spec.Argon2.deriveSig, X86_64.abi,
    X86_64.argRegs, X86_64.stackArg, X86_64.stackArgAddr, List.range, List.range.loop,
    satState, satMem, satArgs, Spec.Argon2.params, Spec.Argon2.valid,
    Spec.Argon2.Params.blocks, Spec.Argon2.Params.segmentLen]

end VG.Proof.Argon2.X86_64.Derive
end

/-! Merged from `Proof.Argon2.X86_64.DeriveCT`. -/
section
/-! The entire entry point leaks only the exact allowance of the shared contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

def AbiRelated (s t : State) : Prop := AbiEnvironment s ∧ AbiEnvironment t ∧ AbiPublic s t

def PrologueRelated (a b : State) : Prop := ∃ s t, AbiRelated s t ∧ a = prologueState s ∧ b = prologueState t

theorem body_rel (v : Proof.Blake2.X86_64.Backend) (name : String) :
    RelCT isa PrologueRelated (Impl.Argon2.X86_64.Derive.body name (HPrime.hash v)) (fun _ _ => True) := by
  have preparation := (prepare_rel.mono (P' := PrologueRelated) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      rw [prologue_sp, prologue_sp, h.2.2.sp]) (fun _ _ h => h)).wpDep (F := fun a b =>
        ∃ s, a = prologueState s ∧ AbiEnvironment s ∧ PrivatePrepared a b) (by
      rintro a b ⟨s, t, h, rfl, rfl⟩
      exact ⟨(prologue_prepare s h.1).mono (fun _ prepared => ⟨s, rfl, h.1, prepared⟩),
        (prologue_prepare t h.2.1).mono (fun _ prepared => ⟨t, rfl, h.2.1, prepared⟩)⟩)
  unfold Impl.Argon2.X86_64.Derive.body
  apply preparation.seq
  apply (RelCT.exists_ (fun p => parameters_body_rel v name p)).mono ?_ (fun _ _ h => h)
  rintro a b ⟨_, x, y, ⟨s, t, h, rfl, rfl⟩,
    ⟨u, hu, _, prepared₁⟩, ⟨w, hw, _, prepared₂⟩⟩
  have left : PrivatePrepared (prologueState s) a := prepared₁
  have right : PrivatePrepared (prologueState t) b := prepared₂
  exact ⟨abiParams s, private_parameters_related h.1 h.2.1 h.2.2 left right⟩

theorem code_ct (v : Proof.Blake2.X86_64.Backend) (name : String) :
    ConstantTime isa (Spec.Argon2.deriveContract X86_64.abi 344).pre
      (Spec.Argon2.deriveContract X86_64.abi 344).pub
      (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v)) := by
  have full := frame_rel Impl.Argon2.X86_64.Derive.saved _ AbiRelated
    (fun _ _ h => h.2.2.sp) (body_rel v name)
  exact (full.mono (fun s t h =>
    ⟨abi_environment s h.1, abi_environment t h.2.1, abi_public s t h.2.2⟩)
    (fun _ _ h => h)).constantTime

end VG.Proof.Argon2.X86_64.Derive
end

/-! Complete Argon2 verification against the reviewed shared API contract. -/

namespace VG.Proof.Argon2.X86_64.Derive

open VG VG.X86_64

theorem verified (v : Proof.Blake2.X86_64.Backend) (name : String) :
    Verified X86_64.target (Impl.Argon2.X86_64.Derive.code name (HPrime.hash v))
      (Spec.Argon2.deriveContract X86_64.abi 344) :=
  ⟨code_correct v name, code_ct v name, contract_sat⟩

end VG.Proof.Argon2.X86_64.Derive
