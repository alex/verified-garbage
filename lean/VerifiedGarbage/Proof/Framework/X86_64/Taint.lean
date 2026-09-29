import VerifiedGarbage.Proof.Framework.X86_64.Taint.Gpr
import VerifiedGarbage.Proof.Framework.X86_64.Taint.Simd

/-!
# Taint tracking for x86-64

Untrusted: everything here is checked by Lean.

The analysis (its abstract state, its step, and what it knows about memory) is
in `Taint/Domain.lean`, and the soundness of its step for each instruction
family in `Taint/Gpr.lean` and `Taint/Simd.lean`. This file puts them together
into `taint`.
-/

namespace VG.X86_64.Taint

theorem step_sound {τ τ' : T} {i : Instr} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : step τ i = some τ') (e₁ : exec i s₁ = some s₁') (e₂ : exec i s₂ = some s₂') :
    addrs i s₁ = addrs i s₂ ∧ Agree τ' s₁' s₂' := by
  cases i with
  | mov _ _ => exact step_sound_mov ha hs e₁ e₂
  | mov32 _ _ => exact step_sound_mov32 ha hs e₁ e₂
  | store _ _ => exact step_sound_store ha hs e₁ e₂
  | store32 _ _ => exact step_sound_store32 ha hs e₁ e₂
  | store8 _ _ => exact step_sound_store8 ha hs e₁ e₂
  | movdquLoad _ _ => exact step_sound_movdquLoad ha hs e₁ e₂
  | movdquStore _ _ => exact step_sound_movdquStore ha hs e₁ e₂
  | xop _ => exact step_sound_xop ha hs e₁ e₂
  | vop _ => exact step_sound_vop ha hs e₁ e₂
  | vmovdquLoad _ _ _ => exact step_sound_vmovdquLoad ha hs e₁ e₂
  | vbroadcasti128 _ _ => exact step_sound_vbroadcasti128 ha hs e₁ e₂
  | vmovdquStore _ _ _ => exact step_sound_vmovdquStore ha hs e₁ e₂
  | stmxcsr _ => exact step_sound_stmxcsr ha hs e₁ e₂
  | ldmxcsr _ => exact step_sound_ldmxcsr ha hs e₁ e₂
  | lfence => exact step_sound_lfence ha hs e₁ e₂
  | alu _ _ _ => exact step_sound_alu ha hs e₁ e₂
  | alu32 _ _ _ => exact step_sound_alu32 ha hs e₁ e₂
  | shift32 _ _ _ => exact step_sound_shift32 ha hs e₁ e₂
  | bswap32 _ => exact step_sound_bswap32 ha hs e₁ e₂
  | movzx8 _ _ => exact step_sound_movzx8 ha hs e₁ e₂
  | bswap _ => exact step_sound_bswap ha hs e₁ e₂
  | shift _ _ _ => exact step_sound_shift ha hs e₁ e₂
  | movImm64 _ _ => exact step_sound_movImm64 ha hs e₁ e₂
  | mul _ => exact step_sound_mul ha hs e₁ e₂

theorem cond_sound {τ : T} {c : Cond} {s₁ s₂ : State} (ha : Agree τ s₁ s₂)
    (hc : τ.flags = true) : eval c s₁ = eval c s₂ := by
  obtain ⟨hcf, hzf, -, -⟩ := ha.rf.2 hc
  cases c <;> simp [eval, hcf, hzf]

theorem Wf.meet_left {τ₁ τ₂ : T} {s : State} (h : Wf τ₁ s) : Wf (meet τ₁ τ₂) s := by
  refine ⟨fun hne => ?_, fun p hp => h.2 p (List.mem_filter.mp hp).1⟩
  by_cases he : τ₁.lens = τ₂.lens
  · simp only [meet, he, ite_true] at hne ⊢; exact he ▸ h.1 (he ▸ hne)
  · simp [meet, he] at hne

theorem Wf.meet_right {τ₁ τ₂ : T} {s : State} (h : Wf τ₂ s) : Wf (meet τ₁ τ₂) s := by
  refine ⟨fun hne => ?_, fun p hp => h.2 p (by simpa using (List.mem_filter.mp hp).2)⟩
  by_cases he : τ₁.lens = τ₂.lens
  · simp only [meet, he, ite_true] at hne ⊢; exact h.1 hne
  · simp [meet, he] at hne

theorem meet_left {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₁ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).1,
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.1)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [exact h.wr hne; exact absurd rfl hne]
  wf₁ := h.wf₁.meet_left
  wf₂ := h.wf₂.meet_left
  lo r hr := h.lo r (RegSet.mem_inter.mp hr).1
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact he ▸ h.ok sl (List.mem_filter.mp hsl).1
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (List.mem_filter.mp hsl).1; cases hsl]

theorem meet_right {τ₁ τ₂ : T} {s₁ s₂ : State} (h : Agree τ₂ s₁ s₂) : Agree (meet τ₁ τ₂) s₁ s₂ where
  rf := ⟨fun r hr => h.rf.1 r (RegSet.mem_inter.mp hr).2,
    fun hf => h.rf.2 (by simp only [meet, Bool.and_eq_true] at hf; exact hf.2)⟩
  wr hne := by
    simp only [meet] at hne
    split at hne <;> [rename_i he; exact absurd rfl hne]
    exact h.wr (he ▸ hne)
  wf₁ := h.wf₁.meet_right
  wf₂ := h.wf₂.meet_right
  lo r hr := h.lo r (RegSet.mem_inter.mp hr).2
  ok sl hsl := by
    simp only [meet] at hsl ⊢
    split at hsl <;> [skip; cases hsl]
    rename_i he; simp only [he, ite_true]; exact h.ok sl (by simpa using (List.mem_filter.mp hsl).2)
  slots sl hsl := by
    simp only [meet] at hsl
    split at hsl <;> [exact h.slots sl (by simpa using (List.mem_filter.mp hsl).2); cases hsl]

theorem le_sound {τ σ : T} {s₁ s₂ : State} (hle : le τ σ = true) (h : Agree σ s₁ s₂) :
    Agree τ s₁ s₂ := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_iff_eq, List.contains_iff_mem] at hle
  obtain ⟨⟨⟨⟨⟨hr, hf⟩, hl⟩, hb⟩, hs⟩, hlo⟩ := hle
  refine ⟨⟨fun r h' => h.rf.1 r (RegSet.mem_of_subset hr h'), fun hf' => h.rf.2 ?_⟩, fun hne => h.wr (hl ▸ hne),
    ⟨fun hne => hl ▸ h.wf₁.1 (hl ▸ hne), fun p hp => h.wf₁.2 p (hb p hp)⟩,
    ⟨fun hne => hl ▸ h.wf₂.1 (hl ▸ hne), fun p hp => h.wf₂.2 p (hb p hp)⟩,
    fun sl hsl => hl ▸ h.ok sl (hs sl hsl), fun sl hsl => h.slots sl (hs sl hsl),
    fun r hr' => h.lo r (RegSet.mem_of_subset hlo hr')⟩
  rcases hf with hf | hf
  · simp [hf'] at hf
  · exact hf

end VG.X86_64.Taint

namespace VG.X86_64

namespace Taint

/-- A call stores its return address, which may differ between the runs, at
`rsp - 8`, which is not known to be outside the writable regions: `rsp` must
be public, and every slot is forgotten. -/
def callStep (τ : T) : Option T :=
  if pub τ .rsp then some { τ with bases := kill τ .rsp, slots := [], lo := .empty } else none

/-- A return loads its return address from `[rsp]` and moves `rsp`. -/
def retStep (τ : T) : Option T :=
  if pub τ .rsp then some { τ with bases := kill τ .rsp, lo := .empty } else none

theorem call_sound {τ τ' : T} {s₁ s₂ s₁' s₂' : State} (ha : Agree τ s₁ s₂)
    (hs : callStep τ = some τ') (e₁ : isa.call s₁ = some s₁') (e₂ : isa.call s₂ = some s₂') :
    isa.callAddrs s₁ = isa.callAddrs s₂ ∧ Agree τ' s₁' s₂' := by
  simp only [callStep] at hs
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  simp only [isa, call, Option.some.injEq] at e₁ e₂
  subst e₁ e₂
  have hsp := ha.reg hp
  refine ⟨by simp [hsp], ⟨⟨fun r hr => ?_, ha.rf.2⟩, ha.wr, ⟨ha.wf₁.1, ?_⟩, ⟨ha.wf₂.1, ?_⟩, ?_, ?_, noLo⟩⟩
  · by_cases h : r = .rsp
    · subst h; simp [State.setReg, hsp]
    · simp only [State.setReg, h, ite_false]; exact ha.rf.1 r hr
  · exact kill_bases (s' := s₁.setReg .rsp (s₁.gpr .rsp - 8)) ha.wf₁ rfl fun _ h => setReg_ne h
  · exact kill_bases (s' := s₂.setReg .rsp (s₂.gpr .rsp - 8)) ha.wf₂ rfl fun _ h => setReg_ne h
  · intro sl h; simp at h
  · intro sl h; simp at h

theorem ret_sound {τ τ' : T} {a₁ a₂ b₁ b₂ c₁ c₂ : State} (ha : Agree τ b₁ b₂)
    (hs : retStep τ = some τ') (e₁ : isa.ret a₁ b₁ = some c₁) (e₂ : isa.ret a₂ b₂ = some c₂) :
    isa.retAddrs b₁ = isa.retAddrs b₂ ∧ Agree τ' c₁ c₂ := by
  simp only [retStep] at hs
  split at hs <;> [rename_i hp; cases hs]
  cases hs
  simp only [isa, ret] at e₁ e₂
  split at e₁ <;> [skip; cases e₁]
  split at e₂ <;> [skip; cases e₂]
  cases e₁; cases e₂
  have hsp := ha.reg hp
  refine ⟨by simp [hsp], ha.keep ⟨fun r hr => ?_, ha.rf.2⟩ rfl rfl rfl rfl rfl rfl
    (kill_setReg ha.wf₁ _ _) (kill_setReg ha.wf₂ _ _) noLo⟩
  by_cases h : r = .rsp
  · subst h; simp [State.setReg, hsp]
  · simp only [State.setReg, h, ite_false]; exact ha.rf.1 r hr

end Taint

/-- Taint tracking for x86-64. -/
def taint : VG.Taint isa where
  T := Taint.T
  Agree := Taint.Agree
  step := Taint.step
  step_sound := Taint.step_sound
  condPub τ _ := τ.flags
  cond_sound := Taint.cond_sound
  meet := Taint.meet
  meet_left := Taint.meet_left
  meet_right := Taint.meet_right
  le := Taint.le
  le_sound := Taint.le_sound
  call := Taint.callStep
  call_sound := Taint.call_sound
  ret := Taint.retStep
  ret_sound := Taint.ret_sound
  -- Frames are not analysed yet.
  push _ _ := none
  push_sound _ h := by cases h
  pop _ _ := none
  pop_sound _ h := by cases h

/-- The taint in which exactly the registers `rs` are public. -/
def Taint.ofRegs (rs : List Reg) : Taint.T := { regs := RegSet.ofList rs, flags := false }

theorem Taint.agree_ofRegs {rs : List Reg} {s₁ s₂ : State}
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) : Taint.Agree (Taint.ofRegs rs) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  ok _ h := by cases h
  slots _ h := by cases h
  lo := noLo

end VG.X86_64
