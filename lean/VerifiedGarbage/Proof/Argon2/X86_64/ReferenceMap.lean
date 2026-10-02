import VerifiedGarbage.Proof.Argon2.X86_64.ReferenceMapFinish

/-! Complete reference mapping against the reviewed RFC specification. -/

namespace VG.Proof.Argon2.X86_64.ReferenceMap

open VG VG.X86_64 VG.Impl.Argon2.X86_64.ReferenceMap

theorem code_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s (Result p pass lane slice index s) := by
  unfold code
  refine WP.seq ((prepareLanes_ok s p pass lane slice index ready).mono ?_)
  intro a ha
  refine WP.seq ((window_ok s a p pass lane slice index ready.bounds ha).mono ?_)
  intro b hb
  refine WP.seq ((relative_ok s b p pass lane slice index ready.bounds hb).mono ?_)
  intro c hc
  exact finish_ok s c p pass lane slice index ready.bounds hc

theorem spec_lane (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).1 = chosenLane p pass lane slice random := rfl

theorem spec_column (p : Spec.Argon2.Params) (pass lane slice index : Nat) (random : Addr) :
    (Spec.Argon2.reference p pass lane slice index random).2 =
      (windowStart p pass slice + relativeValue p pass lane slice index random) % p.laneLen := rfl

theorem code_spec_ok (s : State) (p : Spec.Argon2.Params) (pass lane slice index : Nat)
    (ready : Ready p pass lane slice index s) :
    WP isa code s fun t =>
      t.gpr .r9 = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).1 ∧
      t.gpr .rdi = BitVec.ofNat 64 (Spec.Argon2.reference p pass lane slice index (s.gpr .rdi)).2 ∧
      t.gpr .r11 = s.gpr .rdi ∧ Divide.Keeps changed s t := by
  refine (code_ok s p pass lane slice index ready).mono ?_
  intro t h
  rw [spec_lane, spec_column]
  exact ⟨h.selected, h.column, h.original, h.keeps⟩

end VG.Proof.Argon2.X86_64.ReferenceMap
