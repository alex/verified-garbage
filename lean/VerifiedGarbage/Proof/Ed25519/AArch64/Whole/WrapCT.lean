import VerifiedGarbage.Proof.Ed25519.AArch64.Whole.Wrap
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Taint

namespace VG.Proof.Ed25519.AArch64.Whole
open VG VG.AArch64 VG.Impl.Ed25519.AArch64.Whole

/-- Relational rule for a register-saving frame. -/
theorem frame_ct {r r' : Reg} {body : Prog isa} {P R : State → State → Prop}
    (hsp : ∀ a b, P a b → a.sp = b.sp)
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = pushed r s ∧ b = pushed r t) body R) :
    RelCT isa P (.frame (.push r) body (.pop r')) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have push_eq : ∀ {a b : State}, isa.push (.push r) a = some b → b = pushed r a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := push_eq ps
      have eb := push_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      have sp₁ := (Exec.rdwr bs).2.2
      have sp₂ := (Exec.rdwr bt).2.2
      have he := hsp s t hp
      refine ⟨?_, trivial⟩
      simp only [addrs, sp₁, sp₂, pushed, he]

/-- Allocating and freeing a buffer emits no data-address leakage. -/
theorem alloc_ct {bytes : Nat} {body : Prog isa} {P R : State → State → Prop}
    (hb : RelCT isa (fun a b => ∃ s t, P s t ∧ a = allocated bytes s ∧ b = allocated bytes t) body R) :
    RelCT isa P (.frame (.alloc bytes) body (.free bytes)) fun _ _ => True := by
  intro s t ts tt s' t' hp es et
  have alloc_eq : ∀ {a b : State}, isa.push (.alloc bytes) a = some b → b = allocated bytes a := by
    intro a b h
    simp only [isa, push] at h
    split at h <;> cases h
    rfl
  cases es with
  | frame ps bs qs =>
    cases et with
    | frame pt bt qt =>
      have ea := alloc_eq ps
      have eb := alloc_eq pt
      subst ea eb
      obtain ⟨rfl, _⟩ := hb _ _ _ _ _ _ ⟨s, t, hp, rfl, rfl⟩ bs bt
      exact ⟨rfl, trivial⟩

/-- The trace from wider permissions is determined by any terminating
execution with the narrowed body permissions. -/
theorem body_trace {c : Prog isa} {s : State} {rd wr : List Region} {P : State → Prop}
    (hb : WP isa c (s.withRegions rd wr) P)
    (hc : Covers (rd ++ wr) (s.rd ++ s.wr)) (hw : Covers wr s.wr)
    {trace : List Leak} {t : State} (he : Exec isa c s trace t) :
    ∃ u, Exec isa c (s.withRegions rd wr) trace u := by
  obtain ⟨tr, u, hu, _⟩ := hb
  have hw' := Exec.widen hu (rd := s.rd) (wr := s.wr) (by simpa using hc) (by simpa using hw)
  simp only [State.withRegions_withRegions, State.withRegions_self] at hw'
  obtain ⟨rfl, _⟩ := Exec.det he hw'
  exact ⟨_, hu⟩

theorem saved_covers {s p : State} (hp : Saved (entered s) 6 p) :
    Covers (bodyRd s ++ bodyWr s) (p.rd ++ p.wr) ∧ Covers (bodyWr s) p.wr := by
  constructor
  · refine Covers.of_sub fun r hr => ?_
    simp only [bodyRd, bodyWr, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [hp.step.rd, hp.step.wr, entered_wr]
    rcases hr with (hr | rfl) | (rfl | hr)
    · exact ⟨r, List.mem_append_left _ hr, 0, by simp⟩
    · exact ⟨⟨base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 256, rfl, by change 256 + 48 ≤ 320; decide⟩
    · exact ⟨⟨base s, 320⟩, List.mem_append_right _ List.mem_cons_self, 0, by simp⟩
    · exact ⟨r, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)), 0, by simp⟩
  · refine Covers.of_sub fun r hr => ?_
    rw [hp.step.wr, entered_wr]
    simp only [bodyWr, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨⟨base s, 320⟩, List.mem_cons_self, 0, by simp⟩
    · exact ⟨r, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr), 0, by simp⟩

theorem saveArgs_ct : RelCT isa (fun s t => s.sp = t.sp) (.block saveArgs) (fun _ _ => True) := by
  refine (RelCT.taint (A := taint) (Taint.ofRegs []) (fun s t h => ?_) (by taint_decide))
  exact ⟨h, fun _ hr => False.elim (by simp at hr)⟩

/-- The saved-argument prologue and both frames preserve body constant time. -/
theorem wrap_ct {body : Prog isa} {Pre : State → Prop} {Pub : State → State → Prop}
    (hsp : ∀ s t, Pub s t → s.sp = t.sp)
    (hb : ∀ s, Pre s → ∀ p, Saved (entered s) 6 p →
      WP isa body (p.withRegions (bodyRd s) (bodyWr s)) (fun _ => True))
    (hct : ∀ s t, Pre s → Pre t → Pub s t → RelCT isa
      (fun a b => ∃ p q, Saved (entered s) 6 p ∧ Saved (entered t) 6 q ∧
        a = p.withRegions (bodyRd s) (bodyWr s) ∧ b = q.withRegions (bodyRd t) (bodyWr t))
      body (fun _ _ => True)) : ConstantTime isa Pre Pub (wrap body) := by
  apply RelCT.constantTime
  refine frame_ct (fun s t h => hsp s t h.2.2) (alloc_ct (R := fun _ _ => True) ?_)
  rintro a b ta tb a' b' ⟨p, q, ⟨s, t, ⟨ps, pt, pub⟩, rfl, rfl⟩, rfl, rfl⟩ ea eb
  cases ea with
  | seq esa eba =>
    cases eb with
    | seq esb ebb =>
      obtain ⟨_, pa, exa, hpa⟩ := saveArgs_ok (s := entered s) (by rw [entered_wr, entered_sp]; exact List.mem_cons_self)
      obtain ⟨_, pb, exb, hpb⟩ := saveArgs_ok (s := entered t) (by rw [entered_wr, entered_sp]; exact List.mem_cons_self)
      obtain ⟨_, rfl⟩ := Exec.det esa exa
      obtain ⟨_, rfl⟩ := Exec.det esb exb
      have trsave := (saveArgs_ct _ _ _ _ _ _ (by
        change (entered s).sp = (entered t).sp
        rw [entered_sp, entered_sp]
        exact congrArg (fun x : Addr => x - 336) (hsp s t pub)) esa esb).1
      obtain ⟨ua, eua⟩ := body_trace (hb s ps _ hpa) (saved_covers hpa).1 (saved_covers hpa).2 eba
      obtain ⟨ub, eub⟩ := body_trace (hb t pt _ hpb) (saved_covers hpb).1 (saved_covers hpb).2 ebb
      have trbody := (hct s t ps pt pub _ _ _ _ _ _ ⟨_, _, hpa, hpb, rfl, rfl⟩ eua eub).1
      exact ⟨by rw [trsave, trbody], trivial⟩

end VG.Proof.Ed25519.AArch64.Whole
