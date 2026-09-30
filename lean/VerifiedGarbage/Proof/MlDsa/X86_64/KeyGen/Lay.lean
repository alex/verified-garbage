import VerifiedGarbage.Proof.MlDsa.X86_64.KeyGen.Base
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA key generation on x86-64: its contract, parameters and buffers

Untrusted: everything here is checked by Lean. The contract the proof is
written against (`kgK p`, which the shared contract implies), the facts about
the parameter sets it uses (`PFacts`), the layout of its buffers (`seed` in
`rbp`; `scratch`, `pk` and `sk` in `rbx`, `r12` and `r13`: `kgR`, `kgW p`),
and the checks of pointers into them, for any parameter set, which `lay`
proves from the offsets by `omega`.
-/

namespace VG.Proof.MlDsa.X86_64.KeyGen

open VG VG.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.MlKem.X86_64 (Ptr sc oSS oSV)
open VG.Impl.MlDsa.X86_64.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : PFacts p := by
  rcases hp with rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## The contract -/

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- `vg_mldsa*_keygen(seed = rdi, pk = rsi, sk = rdx, scratch = rcx) -> eax`, with 24 bytes of stack. -/
def kgK (p : Params) : Contract isa where
  pre s :=
    24 ≤ (s.gpr .rsp).toNat ∧
    s.rd = [⟨s.gpr .rdi, 32⟩] ∧ s.wr = [⟨s.gpr .rsi, p.pkLen⟩, ⟨s.gpr .rdx, p.skLen⟩, ⟨s.gpr .rcx, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rsi, p.pkLen⟩ ∧ Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rdx, p.skLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rdi, 32⟩ ⟨s.gpr .rcx, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ⟨s.gpr .rdx, p.skLen⟩ ∧
    Region.Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ⟨s.gpr .rcx, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .rdx, p.skLen⟩ ⟨s.gpr .rcx, scrLen p⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdi, 32⟩ ∧ (retR s).Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ∧
    (retR s).Disjoint ⟨s.gpr .rdx, p.skLen⟩ ∧ (retR s).Disjoint ⟨s.gpr .rcx, scrLen p⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdi, 32⟩ ∧ (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rsi, p.pkLen⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rdx, p.skLen⟩ ∧
    (below (s.gpr .rsp) 24).Disjoint ⟨s.gpr .rcx, scrLen p⟩ ∧
    (s.gpr .rdi).toNat + 32 ≤ 2 ^ 64 ∧ (s.gpr .rsi).toNat + p.pkLen ≤ 2 ^ 64 ∧
    (s.gpr .rdx).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .rcx).toNat + scrLen p ≤ 2 ^ 64
  post s s' :=
    Spec.MlDsa.Outcome (fun b => Spec.MlDsa.keyGenInternal p b (bytesAt s.mem (s.gpr .rdi) 32))
      ((s'.gpr .rax).setWidth 32) (bytesAt s'.mem (s.gpr .rsi) p.pkLen, bytesAt s'.mem (s.gpr .rdx) p.skLen)
  pub s₁ s₂ := s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .rsp = s₂.gpr .rsp ∧
    Spec.MlDsa.keyGenLeak p (bytesAt s₁.mem (s₁.gpr .rdi) 32) = Spec.MlDsa.keyGenLeak p (bytesAt s₂.mem (s₂.gpr .rdi) 32)

/-! ## The layout -/

/-- The pointers the function keeps. -/
abbrev kgM : List (Reg × Reg) := [(.rbx, .rcx), (.rbp, .rdi), (.r12, .rsi), (.r13, .rdx)]
/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.rbp, 32)]
/-- `scratch`, `pk` and `sk`. -/
abbrev kgW (p : Params) : List (Reg × Nat) := [(.rbx, scrLen p), (.r12, p.pkLen), (.r13, p.skLen)]
abbrev kgB (p : Params) : List (Reg × Nat) := kgR ++ kgW p

theorem kgB_bases (p : Params) : ∀ b ∈ kgB p, b.1 ∈ bases := fun b hb => by
  simp only [kgB, kgR, kgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp [bases]
theorem kgM_bases : ∀ q ∈ kgM, q.1 ∈ bases := by decide

theorem kgLay {p : Params} (hF : PFacts p) {σ s : State} (hp : (kgK p).pre σ) (h : Top kgM σ s) :
    Lay kgR (kgW p) s := by
  obtain ⟨_, hrd, hwr, d1, d2, d3, d4, d5, d6, r1, r2, r3, r4, k1, k2, k3, k4, n1, n2, n3, n4⟩ := hp
  have e1 : s.gpr .rbx = σ.gpr .rcx := h.regs (.rbx, .rcx) (by decide)
  have e2 : s.gpr .rbp = σ.gpr .rdi := h.regs (.rbp, .rdi) (by decide)
  have e3 : s.gpr .r12 = σ.gpr .rsi := h.regs (.r12, .rsi) (by decide)
  have e4 : s.gpr .r13 = σ.gpr .rdx := h.regs (.r13, .rdx) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have hs : scrLen p < 2 ^ 32 := by
    have := hF.k; have := hF.l; have := hF.kl; simp only [scrLen, scratchWords]; omega
  have hpk : p.pkLen < 2 ^ 32 := by rw [hF.pk]; have := hF.k; omega
  have hsk : p.skLen < 2 ^ 32 := by
    rw [hF.sk]; have := hF.k; have := hF.l
    rcases hF.eta with ⟨_, he⟩ | ⟨_, he⟩ <;> simp only [oT0, he] <;> omega
  refine Lay.of (fa4 (by decide) hs hpk hsk) (pw4 ?_ ?_ ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_)
    (fa4 ?_ ?_ ?_ ?_) (fa3 ?_ ?_ ?_) (fa4 ?_ ?_ ?_ ?_) <;> simp only [e1, e2, e3, e4, h.rsp, retR]
  · exact fun _ => d3
  · exact fun _ => d1
  · exact fun _ => d2
  · exact fun _ => d5.symm
  · exact fun _ => d6.symm
  · exact fun _ => d4
  exacts [k1, k4, k2, k3, n1, n4, n2, n3,
    mem ⟨σ.gpr .rdi, 32⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .rcx, scrLen p⟩ (by rw [hwr]; simp),
    mem ⟨σ.gpr .rsi, p.pkLen⟩ (by rw [hwr]; simp), mem ⟨σ.gpr .rdx, p.skLen⟩ (by rw [hwr]; simp),
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩,
    ⟨_, by rw [h.wr, hwr]; simp, Region.contains_self _ _⟩, r1, r4, r2, r3]

/-! ## Checks of pointers, by `omega` -/

theorem inB_rbp (p : Params) (o l : Nat) : inB (kgB p) (.rbp, o) l = decide (o + l ≤ 32) := rfl
theorem inB_rbx (p : Params) (o l : Nat) : inB (kgB p) (.rbx, o) l = decide (o + l ≤ scrLen p) := rfl
theorem inB_r12 (p : Params) (o l : Nat) : inB (kgB p) (.r12, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_r13 (p : Params) (o l : Nat) : inB (kgB p) (.r13, o) l = decide (o + l ≤ p.skLen) := rfl
theorem inB_rbxW (p : Params) (o l : Nat) : inB (kgW p) (.rbx, o) l = decide (o + l ≤ scrLen p) := rfl
theorem inB_r12W (p : Params) (o l : Nat) : inB (kgW p) (.r12, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_r13W (p : Params) (o l : Nat) : inB (kgW p) (.r13, o) l = decide (o + l ≤ p.skLen) := rfl

theorem sepB_same (bs : List (Reg × Nat)) (r : Reg) (o l o' l' : Nat) :
    sepB bs (r, o) l (r, o') l' = (inB bs (r, o) l && inB bs (r, o') l' && (decide (o + l ≤ o') || decide (o' + l' ≤ o))) := by
  simp [sepB]

theorem sepB_diff (bs : List (Reg × Nat)) {r r' : Reg} (h : r ≠ r') (hw : r ∈ wRegs ∨ r' ∈ wRegs) (o l o' l' : Nat) :
    sepB bs (r, o) l (r', o') l' = (inB bs (r, o) l && inB bs (r', o') l') := by
  have h1 : (r != r') = true := bne_iff_ne.mpr h
  have h2 : (r == r') = false := beq_eq_false_iff_ne.mpr h
  have h3 : (decide (r ∈ wRegs) || decide (r' ∈ wRegs)) = true := by simpa using hw
  simp only [sepB, h1, h2, h3, Bool.false_and, Bool.or_false, Bool.and_true]

/-- The pairs of distinct registers of the layout, one of them written. -/
theorem sepB_bx_bp (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbx, o) l (.rbp, o') l' = (inB bs (.rbx, o) l && inB bs (.rbp, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bp_bx (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbp, o) l (.rbx, o') l' = (inB bs (.rbp, o) l && inB bs (.rbx, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bx_12 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbx, o) l (.r12, o') l' = (inB bs (.rbx, o) l && inB bs (.r12, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_12_bx (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r12, o) l (.rbx, o') l' = (inB bs (.r12, o) l && inB bs (.rbx, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bx_13 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbx, o) l (.r13, o') l' = (inB bs (.rbx, o) l && inB bs (.r13, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_13_bx (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r13, o) l (.rbx, o') l' = (inB bs (.r13, o) l && inB bs (.rbx, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_12_13 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r12, o) l (.r13, o') l' = (inB bs (.r12, o) l && inB bs (.r13, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_13_12 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r13, o) l (.r12, o') l' = (inB bs (.r13, o) l && inB bs (.r12, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bp_12 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbp, o) l (.r12, o') l' = (inB bs (.rbp, o) l && inB bs (.r12, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_12_bp (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r12, o) l (.rbp, o') l' = (inB bs (.r12, o) l && inB bs (.rbp, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_bp_13 (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.rbp, o) l (.r13, o') l' = (inB bs (.rbp, o) l && inB bs (.r13, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'
theorem sepB_13_bp (bs : List (Reg × Nat)) (o l o' l' : Nat) :
    sepB bs (.r13, o) l (.rbp, o') l' = (inB bs (.r13, o) l && inB bs (.rbp, o') l') :=
  sepB_diff bs (by decide) (by decide) o l o' l'

/-- Unfolds the checks of pointers into the layout into arithmetic, then
`omega` (in each case of `η`). -/
syntax "lay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lay) => `(tactic| lay [])
  | `(tactic| lay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlKem.X86_64.keepB, VG.Proof.MlDsa.X86_64.KeyGen.sepB_same,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bx_bp, VG.Proof.MlDsa.X86_64.KeyGen.sepB_bp_bx,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bx_12, VG.Proof.MlDsa.X86_64.KeyGen.sepB_12_bx,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bx_13, VG.Proof.MlDsa.X86_64.KeyGen.sepB_13_bx,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_12_13, VG.Proof.MlDsa.X86_64.KeyGen.sepB_13_12,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bp_12, VG.Proof.MlDsa.X86_64.KeyGen.sepB_12_bp,
        VG.Proof.MlDsa.X86_64.KeyGen.sepB_bp_13, VG.Proof.MlDsa.X86_64.KeyGen.sepB_13_bp,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_rbp, VG.Proof.MlDsa.X86_64.KeyGen.inB_rbx,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_r12, VG.Proof.MlDsa.X86_64.KeyGen.inB_r13,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_rbxW, VG.Proof.MlDsa.X86_64.KeyGen.inB_r12W,
        VG.Proof.MlDsa.X86_64.KeyGen.inB_r13W, List.all_cons, List.all_nil,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, true_and, and_true, $ls,*]
      set_option linter.unusedSimpArgs false in
      try simp only [VG.Proof.MlDsa.X86_64.KeyGen.scrLen, VG.Spec.MlDsa.scratchWords,
        VG.Impl.MlDsa.X86_64.KeyGen.oP, VG.Impl.MlDsa.X86_64.KeyGen.oSA, VG.Impl.MlDsa.X86_64.KeyGen.oSB,
        VG.Impl.MlDsa.X86_64.KeyGen.oHX, VG.Impl.MlDsa.X86_64.KeyGen.oKL, VG.Impl.MlKem.X86_64.oSS,
        VG.Impl.MlKem.X86_64.oSV, VG.Impl.MlDsa.X86_64.KeyGen.oT0]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.X86_64.KeyGen
