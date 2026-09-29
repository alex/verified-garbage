import VerifiedGarbage.Spec.MlKem.Poly
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86-64: the contracts the proofs are written against

Untrusted: everything here is checked by Lean. For each function, a
contract with the facts of its shared contract (`Spec/MlKem/Poly.lean`,
`Spec/MlKem/Contract.lean`) spelled out for x86-64: the arguments in their
registers, the permitted regions, their disjointness, and the
postcondition. The proofs are written against these, and callers use them
(`WP.call`); `Verified.of_correct` moves a proof to the shared contract,
which implies it (`sig_implies`).
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64
open VG.Spec.MlKem

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A polynomial, at `p`. -/
abbrev pR (p : Addr) : Region := ⟨p, 1024⟩

/-- `vg_mlkem_add(f = rdi, g = rsi)` and `vg_mlkem_sub(f = rdi, g = rsi)`:
`f` becomes `t f g`. -/
def accK (t : Poly → Poly → Poly) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rdi)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint (pR (s.gpr .rsi)) ∧ Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)
  post s s' := PolyIs s'.mem (s.gpr .rdi) (t (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi)))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_encode12(f = rdi, out = rsi)`. -/
def encode12K : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [⟨s.gpr .rsi, 384⟩] ∧
    (pR (s.gpr .rdi)).Disjoint ⟨s.gpr .rsi, 384⟩ ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint ⟨s.gpr .rsi, 384⟩ ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := Spec.Sha3.bytesAt s'.mem (s.gpr .rsi) 384 = encode12 (polyAt s.mem (s.gpr .rdi))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_decode12(b = rdi, f = rsi)`. -/
def decode12K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 384⟩] ∧ s.wr = [pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 384⟩ (pR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 384⟩ ∧
    (retR s).Disjoint (pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi) (decode12 (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 384))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-- `vg_mlkem_cbd2(b = rdi, f = rsi)`. -/
def cbd2K : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .rdi, 128⟩] ∧ s.wr = [pR (s.gpr .rsi)] ∧
    Region.Disjoint ⟨s.gpr .rdi, 128⟩ (pR (s.gpr .rsi)) ∧ (retR s).Disjoint ⟨s.gpr .rdi, 128⟩ ∧
    (retR s).Disjoint (pR (s.gpr .rsi))
  post s s' := PolyIs s'.mem (s.gpr .rsi) (samplePolyCBD 2 (Spec.Sha3.bytesAt s.mem (s.gpr .rdi) 128))
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rsp = s₂.gpr .rsp

/-! ## Satisfiability -/

theorem read_zero (a : Addr) : ∀ n, Mem.read (fun _ => 0) a n = 0
  | 0 => rfl
  | n + 1 => by
    rw [Mem.read, read_zero (a + 1) n]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_append]
    have (w : Nat) : (0 : BitVec w).toNat = 0 := BitVec.toNat_zero
    rw [this, this, this]
    rfl

/-- In memory of zeros, every polynomial is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun _ _ => by
  simp only [coeffAt, Mem.readW, read_zero]
  decide

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
syntax "mlkem_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mlkem_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

end VG.Proof.MlKem.X86_64
