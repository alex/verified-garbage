import VerifiedGarbage.Proof.Argon2.X86.Derive.CTBase

/-!
# Argon2 on x86 (32-bit): two runs of the body

`Two s₀₁ s₀₂`: two runs of the derivation with the same public data.
`Two.leaf` relates a piece of the body the taint analysis proves, from the
public words of the locals (`slots_of_words`), and adds what each run
satisfies by correctness; `ccall_rel` and `hcall_rel` relate the calls of G
and H′, from their preconditions in both runs and their public arguments.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.Proof.Argon2.X86 (compressX86)

/-- Two runs of the derivation, with the same public data. -/
structure Two (s₀₁ s₀₂ : State) : Prop where
  hp₁ : DPre s₀₁
  hp₂ : DPre s₀₂
  pb : Pub2 s₀₁ s₀₂

namespace Pub2
variable {s₀₁ s₀₂ : State} (h : Pub2 s₀₁ s₀₂)
include h

theorem arg_eq {i : Nat} (hi : i < 18) : arg s₀₁ i = arg s₀₂ i := h.2 i hi
theorem memP_eq : memP s₀₁ = memP s₀₂ := h.2 13 (by decide)
theorem scrP_eq : scrP s₀₁ = scrP s₀₂ := h.2 15 (by decide)
theorem outP_eq : outP s₀₁ = outP s₀₂ := h.2 16 (by decide)
theorem outL_eq : outL s₀₁ = outL s₀₂ := by simp only [outL, h.2 17 (by decide)]
theorem blocksN_eq : blocksN s₀₁ = blocksN s₀₂ := by simp only [blocksN, h.2 14 (by decide)]
theorem lanesN_eq : lanesN s₀₁ = lanesN s₀₂ := by simp only [lanesN, h.2 7 (by decide)]
theorem itersN_eq : itersN s₀₁ = itersN s₀₂ := by simp only [itersN, h.2 5 (by decide)]

theorem prm_eq : prm s₀₁ = prm s₀₂ := by
  simp only [prm, kindV, itersN, mcostN, lanesN, outL, h.2 0 (by decide), h.2 5 (by decide),
    h.2 6 (by decide), h.2 7 (by decide), h.2 17 (by decide)]

theorem esp_eq : s₀₁.gpr .esp = s₀₂.gpr .esp := h.1

end Pub2

/-- The slots `sl` of the locals hold the words `ws`. -/
theorem slots_of_words {s₀₁ s₀₂ s₁ s₂ : State} {ws : List Nat} {sl : List (Nat × Nat × Nat)}
    (hw : ∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d)
    (hc : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws) :
    ∀ x ∈ sl, x.1 = 0 ∧ ∀ k, x.2.1 ≤ k → k < x.2.1 + x.2.2 →
      lw s₀₁ s₁ (4 * (k / 4)) = lw s₀₂ s₂ (4 * (k / 4)) := by
  intro x hx
  obtain ⟨h0, hj⟩ := hc x hx
  refine ⟨h0, fun k h₁ h₂ => hw _ ?_⟩
  have := hj (k - x.2.1) (by omega)
  rwa [Nat.add_sub_cancel' h₁] at this

/-- A relation proved for each pair of related states. -/
theorem RelCT.of_eq {P Q : State → State → Prop} {c : Prog isa}
    (h : ∀ s₁ s₂, P s₁ s₂ → RelCT isa (fun a b => a = s₁ ∧ b = s₂) c Q) : RelCT isa P c Q :=
  fun s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂ => h s₁ s₂ hp s₁ s₂ t₁ t₂ s₁' s₂' ⟨rfl, rfl⟩ e₁ e₂

theorem execBlock_append (l₁ l₂ : List Instr) (s : State) :
    execBlock isa (l₁ ++ l₂) s = (execBlock isa l₁ s).bind fun p =>
      (execBlock isa l₂ p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction l₁ generalizing s with
  | nil => simp [execBlock]
  | cons i is ih =>
    simp only [List.cons_append, execBlock]
    split
    · rfl
    · rw [ih]
      cases execBlock isa is _ with
      | none => rfl
      | some p => simp [Function.comp_def, List.append_assoc]

/-- A block in two parts leaks as their sequence. -/
theorem RelCT.block_split {P Q : State → State → Prop} {l₁ l₂ : List Instr}
    (h : RelCT isa P (.seq (.block l₁) (.block l₂)) Q) : RelCT isa P (.block (l₁ ++ l₂)) Q := by
  have split : ∀ {s t s'}, Exec isa (.block (l₁ ++ l₂)) s t s' →
      Exec isa (.seq (.block l₁) (.block l₂)) s t s' := by
    intro s t s' e
    rw [Exec.block_iff, execBlock_append, Option.bind_eq_some_iff] at e
    obtain ⟨⟨s₁, t₁⟩, h₁, h₂⟩ := e
    rw [Option.map_eq_some_iff] at h₂
    obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h₂
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact .seq (.block h₁) (.block h₂)
  exact fun _ _ _ _ _ _ hp e₁ e₂ => h _ _ _ _ _ _ hp (split e₁) (split e₂)

namespace Two
variable {s₀₁ s₀₂ : State} (T : Two s₀₁ s₀₂)
include T

/-- A piece of the body the taint analysis proves, from the slots `sl` of the
locals, which hold the words `ws`, public; with what each run satisfies. -/
theorem leaf {F₁ F₂ G₁ G₂ : State → Prop} {c : Prog isa} (ws : List Nat) (sl : List (Nat × Nat × Nat))
    (rs : List Reg) (hok : VG.X86.Taint.SlotsOk (τB sl rs))
    (hsl : ∀ x ∈ sl, x.1 = 0 ∧ ∀ j < x.2.2, 4 * ((x.2.1 + j) / 4) ∈ ws)
    (hag : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ → Inv s₀₁ s₁ ∧ Inv s₀₂ s₂ ∧ (∀ d ∈ ws, lw s₀₁ s₁ d = lw s₀₂ s₂ d) ∧
      ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hc : ∃ hc, (VG.Taint.check taint (τB sl rs) c hc).isSome = true)
    (hw₁ : ∀ s, F₁ s → WP isa c s G₁) (hw₂ : ∀ s, F₂ s → WP isa c s G₂) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) c fun t₁ t₂ => G₁ t₁ ∧ G₂ t₂ :=
  (rel_taintW (R := fun _ _ => True) (τB sl rs) (fun s₁ s₂ f₁ f₂ _ => by
      obtain ⟨i₁, i₂, hw, hr⟩ := hag s₁ s₂ f₁ f₂
      exact agreeB T.hp₁ T.hp₂ T.pb i₁ i₂ sl rs hr hok (slots_of_words hw hsl)) hc hw₁ hw₂).mono
    (fun _ _ h => ⟨h.1, h.2, trivial⟩) fun _ _ h => h

/-- A call of G: `compress(eax, esi, ecx, edx)` to `scratch + o`, with the
same blocks in both runs. -/
theorem ccall_rel {o : Nat} (ho : 4096 ≤ o) (ho' : o + 1024 ≤ 16384) {F₁ F₂ : State → Prop}
    (h : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .edx = scrP s₀₁ ∧ s₁.gpr .ecx = scrP s₀₁ + BitVec.ofNat 32 o ∧
        GArg s₀₁ o (s₁.gpr .eax) ∧ GArg s₀₁ o (s₁.gpr .esi)) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .edx = scrP s₀₂ ∧ s₂.gpr .ecx = scrP s₀₂ + BitVec.ofNat 32 o ∧
        GArg s₀₂ o (s₂.gpr .eax) ∧ GArg s₀₂ o (s₂.gpr .esi)) ∧
      s₁.gpr .eax = s₂.gpr .eax ∧ s₁.gpr .esi = s₂.gpr .esi) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) Impl.Argon2.X86.Derive.compressCall fun _ _ => True := by
  refine RelCT.of_eq fun s₁ s₂ ⟨f₁, f₂⟩ => ?_
  obtain ⟨⟨i₁, d₁, c₁, x₁, y₁⟩, ⟨i₂, d₂, c₂, x₂, y₂⟩, ea, es⟩ := h s₁ s₂ f₁ f₂
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by rw [i₁.esp, i₂.esp, T.pb.E]
  have p₁ := ccall_pre T.hp₁ i₁ d₁ ho ho' c₁ x₁ y₁
  have p₂ := ccall_pre T.hp₂ i₂ d₂ ho ho' c₂ x₂ y₂
  rw [← ea, ← es, ← hsp, show scrB s₀₂ = scrB s₀₁ by rw [scrB, scrB, T.pb.scrP_eq]] at p₂
  unfold Impl.Argon2.X86.Derive.compressCall
  refine RelCT.callWith (k := compressX86) Proof.Argon2.X86.compress_verified.1
    Proof.Argon2.X86.compress_verified.2.1
    [⟨(s₁.gpr .eax).setWidth 64, 1024⟩, ⟨(s₁.gpr .esi).setWidth 64, 1024⟩,
      ⟨(s₁.gpr .esp - BitVec.ofNat 32 16).setWidth 64, 16⟩]
    [⟨scrB s₀₁ + BitVec.ofNat 64 o, 1024⟩, ⟨scrB s₀₁, 4096⟩] fun a b ⟨ha, hb⟩ => ?_
  subst ha hb
  have fit : 4 * [Reg.edx, .ecx, .esi, .eax].length + 4 ≤ (a.gpr .esp).toNat := by
    have := T.hp₁.esp_lo
    rw [i₁.esp, E_nat T.hp₁]; simp only [List.length_cons, List.length_nil]; omega
  obtain ⟨q₁, q₂⟩ := HPrime.call_pub (by decide) fit hsp (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [d₁, d₂, T.pb.scrP_eq]
    · rw [c₁, c₂, T.pb.scrP_eq]
    · exact es
    · exact ea) _ _
  exact ⟨p₁, p₂, hsp, q₁, q₂⟩

/-- A call of H′: `hprime(r, eax, edi, ecx, edx)`, with the same arguments in
both runs. -/
theorem hcall_rel {r : Reg} (hr : r ≠ .esp) {F₁ F₂ : State → Prop}
    (h : ∀ s₁ s₂, F₁ s₁ → F₂ s₂ →
      (Inv s₀₁ s₁ ∧ s₁.gpr .edx = scrP s₀₁ ∧
        (∃ R ∈ [memR s₀₁, locR s₀₁], ∃ off, (s₁.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .eax).toNat ≤ R.len) ∧ (s₁.gpr r).toNat + (s₁.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₁, outR s₀₁], ∃ off, (s₁.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₁.gpr .ecx).toNat ≤ R.len) ∧ (s₁.gpr .edi).toNat + (s₁.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₁.gpr .ecx).toNat) ∧
      (Inv s₀₂ s₂ ∧ s₂.gpr .edx = scrP s₀₂ ∧
        (∃ R ∈ [memR s₀₂, locR s₀₂], ∃ off, (s₂.gpr r).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .eax).toNat ≤ R.len) ∧ (s₂.gpr r).toNat + (s₂.gpr .eax).toNat ≤ 2 ^ 32 ∧
        (∃ R ∈ [memR s₀₂, outR s₀₂], ∃ off, (s₂.gpr .edi).setWidth 64 = R.base + BitVec.ofNat 64 off ∧
          off + (s₂.gpr .ecx).toNat ≤ R.len) ∧ (s₂.gpr .edi).toNat + (s₂.gpr .ecx).toNat ≤ 2 ^ 32 ∧
        1 ≤ (s₂.gpr .ecx).toNat) ∧
      s₁.gpr r = s₂.gpr r ∧ s₁.gpr .eax = s₂.gpr .eax ∧ s₁.gpr .edi = s₂.gpr .edi ∧
        s₁.gpr .ecx = s₂.gpr .ecx) :
    RelCT isa (fun s₁ s₂ => F₁ s₁ ∧ F₂ s₂) (.frame (.push [.edx, .ecx, .edi, .eax, r])
      (.call Impl.Argon2.X86.Derive.hPrimeName Impl.Argon2.X86.HPrime.code) (.pop .eax 5)) fun _ _ => True := by
  refine RelCT.of_eq fun s₁ s₂ ⟨f₁, f₂⟩ => ?_
  obtain ⟨⟨i₁, d₁, n₁, nf₁, o₁, of₁, l₁⟩, ⟨i₂, d₂, n₂, nf₂, o₂, of₂, l₂⟩, er, ea, ed, ec⟩ := h s₁ s₂ f₁ f₂
  have hsp : s₁.gpr .esp = s₂.gpr .esp := by rw [i₁.esp, i₂.esp, T.pb.E]
  have p₁ := hcall_pre T.hp₁ i₁ hr d₁ n₁ nf₁ o₁ of₁ l₁
  have p₂ := hcall_pre T.hp₂ i₂ hr d₂ n₂ nf₂ o₂ of₂ l₂
  rw [← er, ← ea, ← ed, ← ec, ← hsp, show scrR s₀₂ = scrR s₀₁ by rw [scrR, scrR, T.pb.scrP_eq]] at p₂
  refine RelCT.callWith (k := HPrime.hPrimeX86) HPrime.hPrime_verified.1 HPrime.hPrime_verified.2.1
    [⟨(s₁.gpr r).setWidth 64, (s₁.gpr .eax).toNat⟩, ⟨(s₁.gpr .esp - BitVec.ofNat 32 20).setWidth 64, 20⟩]
    [⟨(s₁.gpr .edi).setWidth 64, (s₁.gpr .ecx).toNat⟩, scrR s₀₁] fun a b ⟨ha, hb⟩ => ?_
  subst ha hb
  have fit : 4 * [Reg.edx, .ecx, .edi, .eax, r].length + 4 ≤ (a.gpr .esp).toNat := by
    have := T.hp₁.esp_lo
    rw [i₁.esp, E_nat T.hp₁]; simp only [List.length_cons, List.length_nil]; omega
  obtain ⟨q₁, q₂⟩ := HPrime.call_pub (by simp [Ne.symm hr]) fit hsp (fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · rw [d₁, d₂, T.pb.scrP_eq]
    · exact ec
    · exact ed
    · exact ea
    · exact er) _ _
  exact ⟨p₁, p₂, hsp, q₁, q₂⟩

end Two

end VG.Proof.Argon2.X86.Derive
