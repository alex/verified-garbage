import VerifiedGarbage.Proof.Rc2.X86.KeyCompose

/-! # A bounded loop rule and frame invariant for key expansion -/

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.Impl.Rc2.X86

theorem forwardLoop (body : Prog isa) (I : Nat → State → Prop) (stop : Nat)
    (step : ∀ i < stop, ∀ s, I i s → WP isa body s (fun s' =>
      I (i + 1) s' ∧ zeroFlag s' = some (decide (i + 1 = stop))))
    (i : Nat) (hi : i < stop) (s : State) (hs : I i s) :
    WP isa (.loop body .ne) s (I stop) := by
  let Inv (n : Nat) (s : State) := ∃ i, i < stop ∧ stop - i = n ∧ I i s
  refine WP.loop (M := isa) Inv ?_ (stop - i) s ⟨i, hi, rfl, hs⟩
  intro n s ⟨j, hj, hn, hI⟩
  apply WP.mono (step j hj s hI)
  intro s' h'
  by_cases he : j + 1 = stop
  · left
    constructor
    · simp only [eval_nonzero, h'.2, he, decide_true, Option.map_some, Bool.not_true]
    · rw [he] at h'
      exact h'.1
  · right
    constructor
    · simp only [eval_nonzero, h'.2, he, decide_false, Option.map_some, Bool.not_false]
    · exact ⟨stop - (j + 1), by omega, j + 1, by omega, rfl, h'.1⟩

/-- Across a key-expansion loop only the four temporaries and the schedule
buffer change. The key, scratch saves, and return address are separate. -/
structure KeyFrame (s₀ s : State) : Prop where
  reg : ∀ r, r ∉ keyTemps → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨addr32 (s₀.gpr .edi), 128⟩] s₀.mem s.mem

theorem KeyFrame.refl (s : State) : KeyFrame s s :=
  ⟨fun _ _ => rfl, rfl, rfl, Frame.refl _ _⟩

theorem KeyFrame.trans {s₀ s₁ s₂ : State} (h₁ : KeyFrame s₀ s₁) (h₂ : KeyFrame s₁ s₂) :
    KeyFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .edi (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem KeyFrame.step {s₀ s s' : State} (h : KeyFrame s₀ s) (i : Nat) (hi : i < 128)
    (b : Byte) (keep : Keep keyTemps {s with mem := s.mem.writeW (addr32 (s₀.gpr .edi) + BitVec.ofNat 64 i) b} s') : KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]
  exact h.mem.writeW List.mem_cons_self _ (Offset.contains_base _ (by omega) (by omega))

theorem KeyFrame.keep {s₀ s s' : State} (h : KeyFrame s₀ s) (keep : Keep keyTemps s s') :
    KeyFrame s₀ s' := by
  refine ⟨fun r hr => (keep.reg r hr).trans (h.reg r hr), keep.rd.trans h.rd,
    keep.wr.trans h.wr, ?_⟩
  rw [keep.mem]; exact h.mem

theorem counter_add (i : Nat) : BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) := by
  rw [BitVec.ofNat_add]
  rfl

theorem counter_eq (i n : Nat) (hi : i < 2 ^ 32) (hn : n < 2 ^ 32) :
    ((BitVec.ofNat 32 i - BitVec.ofNat 32 n) == 0#32) = decide (i = n) := by
  have he : (BitVec.ofNat 32 i - BitVec.ofNat 32 n = 0#32) ↔ i = n := by bv_omega
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, decide_eq_true_eq] using he

theorem counter_sub (i : Nat) (hi : 1 ≤ i) :
    BitVec.ofNat 32 i - 1 = BitVec.ofNat 32 (i - 1) :=
  Offset.ofNat_sub_ofNat hi

end VG.Proof.Rc2.X86
