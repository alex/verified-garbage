import VerifiedGarbage.Proof.Argon2.AArch64.DerivePublic
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveInputBytes
import VerifiedGarbage.Proof.Argon2.AArch64.DeriveParametersCT

/-! Private argument copies retain exactly the reviewed public relation. -/

namespace VG.Proof.Argon2.AArch64.Derive

open VG VG.AArch64
open VG.Proof.Argon2.AArch64.Initial (wordAt)

theorem DeriveWords.public_words {s₁ s₂ t₁ t₂ : State} (h : AbiPublic s₁ s₂)
    (left : DeriveWords s₁ t₁) (right : DeriveWords s₂ t₂) :
    ∀ d ∈ Initial.slots, wordAt t₁ d = wordAt t₂ d := by
  intro d hd
  simp only [Initial.slots, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [left.passes, right.passes, h.params]
  · rw [left.saltLength, right.saltLength]; exact h.regs .x4 (by simp)
  · rw [left.salt, right.salt]; exact h.regs .x3 (by simp)
  · rw [left.passwordLength, right.passwordLength]; exact h.regs .x2 (by simp)
  · rw [left.password, right.password]; exact h.regs .x1 (by simp)
  · rw [left.kind, right.kind, h.params]
  · rw [left.memory, right.memory, h.params]
  · rw [left.lanes, right.lanes, h.params]
  · rw [left.secret, right.secret]; exact h.words 8 (by simp)
  · rw [left.secretLength, right.secretLength]; exact h.words 16 (by simp)
  · rw [left.ad, right.ad]; exact h.words 24 (by simp)
  · rw [left.adLength, right.adLength]; exact h.words 32 (by simp)
  · rw [left.tagLength, right.tagLength, h.params]

def abiReferences (s : State) : List Nat := Spec.Argon2.references (abiParams s)
  (Spec.Blake2.bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
  (Spec.Blake2.bytesAt s.mem (s.gpr .x3) (s.gpr .x4).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 8) (abiWord s 16).toNat)
  (Spec.Blake2.bytesAt s.mem (abiWord s 24) (abiWord s 32).toNat)

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
  have sp : t₁.sp = t₂.sp := by rw [prepared₁.sp, prepared₂.sp, prologue_sp, prologue_sp, h.sp]
  have bp : t₁.gpr .x19 = t₂.gpr .x19 := by rw [prepared₁.bp, prepared₂.bp, prologue_sp, prologue_sp, h.sp]
  have bx : t₁.gpr .x24 = t₂.gpr .x24 := by
    rw [private_scratch left prepared₁, private_scratch right prepared₂]
    exact h.words 56 (by simp)
  refine ⟨private_parameters left prepared₁, same.symm ▸ private_parameters right prepared₂, ?_⟩
  refine ⟨ready₁, ready₂, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨ready₁.hashSpace, ready₁.inputs⟩,
      ⟨ready₂.hashSpace, ready₂.inputs⟩, ?_, ?_, ?_, ?_⟩
    · rw [keeps₁.bp, keeps₂.bp]; exact bp
    · rw [keeps₁.bx, keeps₂.bx]; exact bx
    · rw [keeps₁.sp, keeps₂.sp]; exact sp
    · exact words₁.public_words h words₂
  · exact words₁.matrix.trans ((h.words 40 (by simp)).trans words₂.matrix.symm)
  · exact words₁.output.trans ((h.words 64 (by simp)).trans words₂.output.symm)
  · exact words₁.work.trans ((h.words 56 (by simp)).trans words₂.work.symm)
  · unfold InitialBody.references
    simp only [keeps₁.inputBytes, keeps₂.inputBytes]
    change InitialBody.references (abiParams s₁) t₁ = InitialBody.references (abiParams s₁) t₂
    rw [private_references left prepared₁, same, private_references right prepared₂]
    exact h.references

end VG.Proof.Argon2.AArch64.Derive
