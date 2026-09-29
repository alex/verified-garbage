import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.X86.CallWith

/-!
# ML-KEM on x86 (32-bit): pieces of code, correct and constant time

Untrusted: everything here is checked by Lean.

A function is proven piece by piece. `Piece Pre Pub A B c` says that, for
every initial state `s₀` satisfying `Pre`, `c` runs from any state
satisfying `A s₀` to one satisfying `B s₀` (`WP`), and that two runs of `c`
from states satisfying `A s₀` and `A s₀'`, for initial states related by
`Pub`, leak the same trace (`RelCT`). The invariants `A` and `B` say what
the correctness proof knows of each run, so a public value (a pointer, a
counter, a loop condition) is public in both runs as soon as correctness
determines it from public data, however it got there (through memory, or a
call). Pieces compose (`seq`, `ite`, `loop`, `frame`, calls of verified code
in a frame of their arguments: `callWith`), straight-line code whose
addresses depend only on registers that correctness determines is checked
by the taint analysis (`taint`), and a whole function from its entry state
gives `Verified` (`verified`).
-/

namespace VG.Proof.MlKem.X86

open VG VG.X86

/-- See the module documentation. -/
structure Piece (Pre : State → Prop) (Pub : State → State → Prop) (A B : State → State → Prop)
    (c : Prog isa) : Prop where
  wp : ∀ s₀ s, Pre s₀ → A s₀ s → WP isa c s (B s₀)
  ct : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' →
    RelCT isa (fun s s' => A s₀ s ∧ A s₀' s') c fun _ _ => True

namespace Piece

variable {Pre : State → Prop} {Pub : State → State → Prop}

/-- Constant time, relating the final states by the postconditions. -/
theorem ct' {A B : State → State → Prop} {c : Prog isa} (h : Piece Pre Pub A B c) {s₀ s₀' : State}
    (h₀ : Pre s₀) (h₀' : Pre s₀') (hp : Pub s₀ s₀') :
    RelCT isa (fun s s' => A s₀ s ∧ A s₀' s') c fun s s' => B s₀ s ∧ B s₀' s' :=
  ((h.ct _ _ h₀ h₀' hp).wp (F₁ := B s₀) (F₂ := B s₀')
    fun _ _ ⟨ha, ha'⟩ => ⟨h.wp _ _ h₀ ha, h.wp _ _ h₀' ha'⟩).mono (fun _ _ h => h)
    fun _ _ ⟨_, b, b'⟩ => ⟨b, b'⟩

theorem mono {A A' B B' : State → State → Prop} {c : Prog isa} (h : Piece Pre Pub A B c)
    (ha : ∀ s₀ s, Pre s₀ → A' s₀ s → A s₀ s) (hb : ∀ s₀ s, Pre s₀ → B s₀ s → B' s₀ s) :
    Piece Pre Pub A' B' c where
  wp s₀ s h₀ h' := (h.wp s₀ s h₀ (ha s₀ s h₀ h')).mono fun _ hb' => hb _ _ h₀ hb'
  ct s₀ s₀' h₀ h₀' hp := (h.ct s₀ s₀' h₀ h₀' hp).mono
    (fun _ _ ⟨a, a'⟩ => ⟨ha _ _ h₀ a, ha _ _ h₀' a'⟩) fun _ _ h => h

/-- Stronger preconditions and public data. -/
theorem pre_mono {Pre' : State → Prop} {Pub' : State → State → Prop} {A B : State → State → Prop}
    {c : Prog isa} (h : Piece Pre Pub A B c) (hp : ∀ s, Pre' s → Pre s)
    (hq : ∀ s s', Pre' s → Pre' s' → Pub' s s' → Pub s s') : Piece Pre' Pub' A B c where
  wp s₀ s h₀ ha := h.wp s₀ s (hp _ h₀) ha
  ct s₀ s₀' h₀ h₀' hpub := h.ct s₀ s₀' (hp _ h₀) (hp _ h₀') (hq _ _ h₀ h₀' hpub)

theorem seq {A B C : State → State → Prop} {c₁ c₂ : Prog isa} (h₁ : Piece Pre Pub A B c₁)
    (h₂ : Piece Pre Pub B C c₂) : Piece Pre Pub A C (.seq c₁ c₂) where
  wp s₀ s h₀ ha := WP.seq ((h₁.wp s₀ s h₀ ha).mono fun s' hb => h₂.wp s₀ s' h₀ hb)
  ct s₀ s₀' h₀ h₀' hp := RelCT.seq (h₁.ct' h₀ h₀' hp) (h₂.ct s₀ s₀' h₀ h₀' hp)

/-- Code the taint analysis proves constant time from the registers `R`,
which correctness determines from public data. -/
theorem taint {A B : State → State → Prop} {c : Prog isa} (R : List Reg)
    (hw : ∀ s₀ s, Pre s₀ → A s₀ s → WP isa c s (B s₀))
    (hR : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      ∀ r ∈ R, s.gpr r = s'.gpr r)
    {hc : Taint.Hint VG.X86.Taint.T} (h : (VG.X86.taint.check (τr R) c hc).isSome = true) :
    Piece Pre Pub A B c where
  wp := hw
  ct _ _ h₀ h₀' hp :=
    RelCT.taint (A := VG.X86.taint) (τr R) (fun _ _ ⟨a, a'⟩ => agree_regs (hR _ _ _ _ h₀ h₀' hp a a')) h

/-- A branch whose condition correctness determines from public data. -/
theorem ite {A B : State → State → Prop} {cnd : Cond} {t e : Prog isa} (b : State → Bool)
    (hb : ∀ s₀ s, Pre s₀ → A s₀ s → isa.eval cnd s = some (b s₀))
    (hbp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → b s₀ = b s₀')
    (ht : Piece Pre Pub (fun s₀ s => A s₀ s ∧ b s₀ = true) B t)
    (he : Piece Pre Pub (fun s₀ s => A s₀ s ∧ b s₀ = false) B e) :
    Piece Pre Pub A B (.ite cnd t e) where
  wp s₀ s h₀ ha := by
    refine WP.ite (b s₀) (hb _ _ h₀ ha) (fun h => ht.wp _ _ h₀ ⟨ha, h⟩) (fun h => he.wp _ _ h₀ ⟨ha, h⟩)
  ct s₀ s₀' h₀ h₀' hp := by
    refine RelCT.ite (fun s s' ⟨a, a'⟩ => by rw [hb _ _ h₀ a, hb _ _ h₀' a', hbp _ _ h₀ h₀' hp])
      ((ht.ct s₀ s₀' h₀ h₀' hp).mono ?_ fun _ _ h => h) ((he.ct s₀ s₀' h₀ h₀' hp).mono ?_ fun _ _ h => h)
    · rintro s s' ⟨⟨a, a'⟩, hc⟩
      rw [hb _ _ h₀ a, Option.some.injEq] at hc
      exact ⟨⟨a, hc⟩, a', by rw [← hbp _ _ h₀ h₀' hp]; exact hc⟩
    · rintro s s' ⟨⟨a, a'⟩, hc⟩
      rw [hb _ _ h₀ a, Option.some.injEq] at hc
      exact ⟨⟨a, hc⟩, a', by rw [← hbp _ _ h₀ h₀' hp]; exact hc⟩

/-- A loop of `N ≥ 1` iterations, with the invariant `Inv k` after `k`. -/
theorem loop {body : Prog isa} {cnd : Cond} (Inv : Nat → State → State → Prop) {N : Nat} (hN : 0 < N)
    (hb : ∀ k < N, Piece Pre Pub (Inv k)
      (fun s₀ s => Inv (k + 1) s₀ s ∧ isa.eval cnd s = some (decide (k + 1 < N))) body) :
    Piece Pre Pub (Inv 0) (Inv N) (.loop body cnd) where
  wp s₀ s h₀ ha := by
    refine WP.loop (M := isa) (fun n (s : State) => ∃ k, n = N - k ∧ k < N ∧ Inv k s₀ s)
      (fun n s hi => ?_) N s ⟨0, (Nat.sub_zero N).symm, hN, ha⟩
    obtain ⟨k, hn, hk, hi⟩ := hi
    refine ((hb k hk).wp _ _ h₀ hi).mono fun s' ⟨hi', hc⟩ => ?_
    by_cases h : k + 1 < N
    · exact .inr ⟨by rw [hc, decide_eq_true h], N - (k + 1), by omega, k + 1, rfl, h, hi'⟩
    · exact .inl ⟨by rw [hc, decide_eq_false h], by rw [show N = k + 1 by omega]; exact hi'⟩
  ct s₀ s₀' h₀ h₀' hp := by
    have := RelCT.loop (M := isa) (body := body) (c := cnd) (Q := fun _ _ => True)
      (fun n s s' => ∃ k, n = N - k ∧ k < N ∧ Inv k s₀ s ∧ Inv k s₀' s')
      (fun n => by
        refine RelCT.exists_ fun k => ?_
        by_cases hk : n = N - k ∧ k < N
        · refine ((hb k hk.2).ct' h₀ h₀' hp).mono (fun s s' ⟨_, _, a, a'⟩ => ⟨a, a'⟩) ?_
          rintro s s' ⟨⟨i₁, c₁⟩, i₂, c₂⟩
          refine ⟨by rw [c₁, c₂], fun _ => trivial, fun h => ?_⟩
          rw [c₁, Option.some.injEq, decide_eq_true_iff] at h
          exact ⟨N - (k + 1), by omega, k + 1, rfl, h, i₁, i₂⟩
        · exact RelCT.of_false fun s s' ⟨h1, h2, _⟩ => hk ⟨h1, h2⟩) N
    exact this.mono (fun s s' ⟨a, a'⟩ => ⟨0, (Nat.sub_zero N).symm, hN, a, a'⟩) fun _ _ h => h

/-- A loop of `N ≥ 1` iterations of a block, counting down with `sub ecx, 1`
(or anything else that leaves the condition `ne` as correctness says),
whose addresses depend only on the registers `R`. -/
theorem countLoop {body : List Instr} {N : Nat} (hN : 0 < N) (Inv : Nat → State → State → Prop)
    (R : List Reg)
    (hstep : ∀ k < N, ∀ s₀ s, Pre s₀ → Inv k s₀ s → WP isa (.block body) s fun s' =>
      Inv (k + 1) s₀ s' ∧ isa.eval .ne s' = some (decide (k + 1 < N)))
    (hR : ∀ k < N, ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → Inv k s₀ s → Inv k s₀' s' →
      ∀ r ∈ R, s.gpr r = s'.gpr r)
    {hc : Taint.Hint VG.X86.Taint.T} (ht : (VG.X86.taint.check (τr R) (.block body) hc).isSome = true) :
    Piece Pre Pub (Inv 0) (Inv N) (.loop (.block body) .ne) :=
  Piece.loop Inv hN fun k hk => Piece.taint R (hstep k hk) (hR k hk) ht

/-- A frame around `body`. -/
theorem frame {A B : State → State → Prop} {rs : List Reg} {r : Reg} {body : Prog isa}
    (hne : rs ≠ []) (hrs : Reg.esp ∉ rs) (hr : r ≠ .esp) (hsp : NoSp body)
    (hn : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length ≤ (s.gpr .esp).toNat)
    (hesp : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      s.gpr .esp = s'.gpr .esp)
    (hb : Piece Pre Pub (fun s₀ s => ∃ s₁, A s₀ s₁ ∧ s = pushed rs s₁)
      (fun s₀ s₂ => B s₀ (popped r rs.length s₂)) body) :
    Piece Pre Pub A B (.frame (.push rs) body (.pop r rs.length)) where
  wp _ s h₀ ha := WP.frame hne hrs hr (hn _ _ h₀ ha) hsp (hb.wp _ _ h₀ ⟨s, ha, rfl⟩)
  ct _ _ h₀ h₀' hp := RelCT.frame (fun _ _ ⟨a, a'⟩ => hesp _ _ _ _ h₀ h₀' hp a a')
    ((hb.ct _ _ h₀ h₀' hp).mono (fun _ _ ⟨s₁, s₂, ⟨h₁, h₂⟩, e₁, e₂⟩ => ⟨⟨s₁, h₁, e₁⟩, s₂, h₂, e₂⟩)
      fun _ _ h => h)

/-- A call of verified code in a frame of its arguments `rs`, with the
permissions `rd s₀` and `wr s₀`. -/
theorem callWith {A B : State → State → Prop} {rs : List Reg} {n : String} {c : Prog isa}
    {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hct : ConstantTime isa k.pre k.pub c) (hsp : NoSp c) (hne : rs ≠ []) (hrs : Reg.esp ∉ rs)
    (rd wr : State → List Region)
    (hd : ∀ s₀ s, Pre s₀ → A s₀ s → 4 * rs.length + stackUse c + 4 ≤ (s.gpr .esp).toNat)
    (hk : ∀ s₀ s, Pre s₀ → A s₀ s → CallPre k rs (rd s₀) (wr s₀) s)
    (hpub : ∀ s₀ s₀' s s', Pre s₀ → Pre s₀' → Pub s₀ s₀' → A s₀ s → A s₀' s' →
      rd s₀ = rd s₀' ∧ wr s₀ = wr s₀' ∧ s.gpr .esp = s'.gpr .esp ∧
      k.pub ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀))
        ((pushed rs s').callEntry.withRegions (rd s₀) (wr s₀)))
    (hQ : ∀ s₀ s s', Pre s₀ → A s₀ s → s'.rd = s.rd → s'.wr = s.wr →
      (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame (wr s₀ ++ [below (s.gpr .esp) (4 * rs.length + stackUse c + 4)]) s.mem s'.mem →
      (∃ s₂ : State, s₂.mem = s'.mem ∧
        k.post ((pushed rs s).callEntry.withRegions (rd s₀) (wr s₀)) s₂) → B s₀ s') :
    Piece Pre Pub A B (.frame (.push rs) (.call n c) (.pop .eax rs.length)) where
  wp s₀ s h₀ ha := WP.callWith hv hsp hne hrs (hd _ _ h₀ ha) (hk _ _ h₀ ha)
    fun s' h₁ h₂ h₃ h₄ h₅ => hQ _ _ _ h₀ ha h₁ h₂ h₃ h₄ h₅
  ct s₀ s₀' h₀ h₀' hp := RelCT.callWith hv hct (rd s₀) (wr s₀) fun s s' ⟨a, a'⟩ => by
    obtain ⟨e₁, e₂, e₃, e₄⟩ := hpub _ _ _ _ h₀ h₀' hp a a'
    exact ⟨hk _ _ h₀ a, e₁ ▸ e₂ ▸ hk _ _ h₀' a', e₃, e₄⟩

/-- A whole function, from its entry state. -/
theorem verified {c : Prog isa} {k : Contract isa}
    (h : Piece k.pre k.pub (fun s₀ s => s = s₀) (fun s₀ s' => abiPreserved s₀ s' ∧ k.post s₀ s') c)
    (hsat : ∃ s, k.pre s) : Verified X86.target c k :=
  ⟨fun s hs => h.wp s s hs rfl,
    fun s₁ s₂ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h.ct s₁ s₂ h₁ h₂ hp _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1, hsat⟩

end Piece

end VG.Proof.MlKem.X86
