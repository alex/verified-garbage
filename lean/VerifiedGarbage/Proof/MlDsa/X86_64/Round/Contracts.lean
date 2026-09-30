import VerifiedGarbage.Spec.MlDsa.Poly
import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.MlDsa.Round.Mem

/-!
# ML-DSA on x86-64: the contracts the rounding proofs are written against

Untrusted: everything here is checked by Lean. For each function, a
contract with the facts of its shared contract (`Spec/MlDsa/Poly.lean`)
spelled out for x86-64: the arguments in their registers, the permitted
regions, their disjointness, and the postcondition. `Verified.of_correct`
moves a proof to the shared contract, which implies it (`round_implies`).
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Proof.MlDsa.Round
open VG.Spec.MlDsa

/-- The return address. -/
abbrev retR (s : State) : Region := ⟨s.gpr .rsp, 8⟩

/-- A `u32` argument in `r`. -/
abbrev arg32 (s : State) (r : Reg) : Nat := ((s.gpr r).setWidth 32).toNat

/-- `vg_mldsa_power2round(t = rdi, t1 = rsi, t0 = rdx)`. -/
def power2RoundK : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .rsi), pR (s.gpr .rdx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rsi)) ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rdx)) ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧
    (retR s).Disjoint (pR (s.gpr .rsi)) ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' :=
    NatPolyIs s'.mem (s.gpr .rsi) ((polyAt s.mem (s.gpr .rdi)).map fun c => (power2Round c).1.toNat) ∧
      PolyIs s'.mem (s.gpr .rdx) ((polyAt s.mem (s.gpr .rdi)).map fun c => ofInt (power2Round c).2)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rsp = s₂.gpr .rsp

/-- `r = rdi, gamma2 = esi, out = rdx`, with the postcondition `post`. -/
def bitsK (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [pR (s.gpr .rdx)] ∧ (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rdx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rdx)) ∧ arg32 s .rsi ∈ gamma2s ∧
    Reduced s.mem (s.gpr .rdi)
  post := post
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `vg_mldsa_high_bits(r = rdi, gamma2 = esi, out = rdx)`. -/
def highBitsK : Contract isa := bitsK fun s s' =>
  NatPolyIs s'.mem (s.gpr .rdx) ((polyAt s.mem (s.gpr .rdi)).map fun c => (highBits (arg32 s .rsi) c).toNat)

/-- `vg_mldsa_low_bits(r = rdi, gamma2 = esi, out = rdx)`. -/
def lowBitsK : Contract isa := bitsK fun s s' =>
  PolyIs s'.mem (s.gpr .rdx) ((polyAt s.mem (s.gpr .rdi)).map fun c => ofInt (lowBits (arg32 s .rsi) c))

/-- `vg_mldsa_norm_lt(f = rdi, bound = esi)`. -/
def normLtK : Contract isa where
  pre s := s.rd = [pR (s.gpr .rdi)] ∧ s.wr = [] ∧ (retR s).Disjoint (pR (s.gpr .rdi)) ∧ Reduced s.mem (s.gpr .rdi)
  post s s' := (s'.gpr .rax).setWidth 32 = if normRq [polyAt s.mem (s.gpr .rdi)] < arg32 s .rsi then 1 else 0
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    (s₁.gpr .rsi).setWidth 32 = (s₂.gpr .rsi).setWidth 32

/-- `a = rdi, b = rsi, gamma2 = edx, out = rcx`, with the precondition
`pre'` on the memory and the postcondition `post`. -/
def hintK (pre' : State → Prop) (post : State → State → Prop) : Contract isa where
  pre s :=
    s.rd = [pR (s.gpr .rdi), pR (s.gpr .rsi)] ∧ s.wr = [pR (s.gpr .rcx)] ∧
    (pR (s.gpr .rdi)).Disjoint (pR (s.gpr .rcx)) ∧ (pR (s.gpr .rsi)).Disjoint (pR (s.gpr .rcx)) ∧
    (retR s).Disjoint (pR (s.gpr .rdi)) ∧ (retR s).Disjoint (pR (s.gpr .rsi)) ∧
    (retR s).Disjoint (pR (s.gpr .rcx)) ∧ arg32 s .rdx ∈ gamma2s ∧ pre' s
  post := post
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rcx = s₂.gpr .rcx ∧
    s₁.gpr .rsp = s₂.gpr .rsp ∧ (s₁.gpr .rdx).setWidth 32 = (s₂.gpr .rdx).setWidth 32

/-- `vg_mldsa_make_hint(z = rdi, r = rsi, gamma2 = edx, h = rcx)`. -/
def makeHintK : Contract isa :=
  hintK (fun s => Reduced s.mem (s.gpr .rdi) ∧ Reduced s.mem (s.gpr .rsi)) fun s s' =>
    let hint := Vector.zipWith (makeHint (arg32 s .rdx)) (polyAt s.mem (s.gpr .rdi)) (polyAt s.mem (s.gpr .rsi))
    HintIs s'.mem (s.gpr .rcx) 1 [hint] ∧ ((s'.gpr .rax).setWidth 32).toNat = hintOnes [hint]

/-- `vg_mldsa_use_hint(h = rdi, r = rsi, gamma2 = edx, out = rcx)`. -/
def useHintK : Contract isa :=
  hintK (fun s => Reduced s.mem (s.gpr .rsi)) fun s s' =>
    NatPolyIs s'.mem (s.gpr .rcx) (Vector.zipWith (fun hj rj => (useHint (arg32 s .rdx) hj rj).toNat)
      ((hintAt s.mem (s.gpr .rdi) 1).headD (Vector.replicate n false)) (polyAt s.mem (s.gpr .rsi)))

/-- The taint in which the registers `rs` are public, and the low halves of
`los` (public 32-bit arguments). -/
def regsLo (rs los : List Reg) : X86_64.Taint.T :=
  { regs := RegSet.ofList rs, flags := false, lo := RegSet.ofList los }

theorem agree_regsLo {rs los : List Reg} {s₁ s₂ : State} (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r)
    (hl : ∀ r ∈ los, (s₁.gpr r).setWidth 32 = (s₂.gpr r).setWidth 32) :
    X86_64.Taint.Agree (regsLo rs los) s₁ s₂ where
  rf := ⟨fun r hr => h r (RegSet.mem_ofList.mp hr), fun h => by cases h⟩
  wr h := absurd rfl h
  wf₁ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  wf₂ := ⟨fun h => absurd rfl h, fun _ h => by cases h⟩
  ok _ h := by cases h
  slots _ h := by cases h
  lo r hr := hl r (RegSet.mem_ofList.mp hr)

/-- `sig_implies`, whose satisfiability witness may need `Reduced` of the
memory of zeros. -/
syntax "round_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| round_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
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

end VG.Proof.MlDsa.X86_64.Round
