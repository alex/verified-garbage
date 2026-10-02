import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.PrimsOk
import VerifiedGarbage.Proof.Framework.Omega

/-!
# ML-DSA key generation on AArch64: parameters and buffers

The facts about the parameter sets the proof uses (`PFacts`), the layout of
the buffers of key generation (`seed` in `x25`, read; `scratch`, `pk` and `sk`
in `x28`, `x26` and `x27`, written: `kgR`, `kgW p`), which the contract's
precondition gives from the prologue on (`kgLay`), and the checks of pointers
into them, for any parameter set, which `lay` proves from the offsets by
`omega`.
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Spec.MlDsa (Params scratchWords mlDsa44 mlDsa65 mlDsa87)
open VG.Spec.Sha3 (bytesAt)

/-! ## The parameter sets -/

/-- What the proof uses of a parameter set. -/
structure PFacts (p : Params) : Prop where
  mem : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87
  k : 1 ≤ p.k ∧ p.k ≤ 8
  l : 1 ≤ p.ℓ ∧ p.ℓ ≤ 7
  kl : p.k * p.ℓ ≤ 56
  eta : (p.η = 2 ∧ lenS p = 96) ∨ (p.η = 4 ∧ lenS p = 128)
  pk : p.pkLen = 32 + 320 * p.k
  sk : p.skLen = oT0 p + 416 * p.k

theorem pfacts {p : Params} (hp : p = mlDsa44 ∨ p = mlDsa65 ∨ p = mlDsa87) : PFacts p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by simp, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The size of `scratch`, in bytes. -/
abbrev scrLen (p : Params) : Nat := scratchWords p * 8

theorem scr_eq (p : Params) : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) := by
  simp only [scrLen, scratchWords]; omega

theorem PFacts.scr {p : Params} (_ : PFacts p) : scrLen p = 1024 * (p.k * p.ℓ + 4 * p.k + 3 * p.ℓ + 32) :=
  scr_eq p

theorem PFacts.small {p : Params} (hF : PFacts p) : scrLen p < 2 ^ 32 ∧ p.pkLen < 2 ^ 32 ∧ p.skLen < 2 ^ 32 := by
  have hk := hF.k; have hl := hF.l; have hkl := hF.kl
  have hls : lenS p * (p.ℓ + p.k) ≤ 128 * 15 := by
    rcases hF.eta with ⟨_, e⟩ | ⟨_, e⟩ <;> rw [e] <;> exact Nat.mul_le_mul (by omega) (by omega)
  refine ⟨by rw [scr_eq]; omega, by rw [hF.pk]; omega, by rw [hF.sk, oT0]; omega⟩

/-! ## The layout -/

/-- `seed`. -/
abbrev kgR : List (Reg × Nat) := [(.x25, 32)]
/-- `scratch`, `pk` and `sk`. -/
abbrev kgW (p : Params) : List (Reg × Nat) := [(.x28, scrLen p), (.x26, p.pkLen), (.x27, p.skLen)]

theorem le_of_wfP {S sp : Nat} (h : wfP S sp) : S ≤ sp := by
  unfold wfP at h; split at h <;> omega

/-- The stack below the stack pointer is apart from the regions, from the
contract's evaluated precondition. -/
theorem below_of_resv {S : Nat} {sp : Addr} {a b c d : Region}
    (h : Sig.conj ((stackBelow sp S).map fun r => [r.Disjoint a, r.Disjoint b, r.Disjoint c, r.Disjoint d]).flatten) :
    (below sp S).Disjoint a ∧ (below sp S).Disjoint b ∧ (below sp S).Disjoint c ∧ (below sp S).Disjoint d := by
  rcases S with _ | S
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> exact fun x h _ => by simp [Region.Contains] at h
  · simp only [stackBelow, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      Sig.conj_cons] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem inR_self {X : List Region} {r : Region} (h : r ∈ X) : InRegions X r.base r.len :=
  ⟨r, h, Region.contains_self _ _⟩

theorem kgLay {p : Params} (hF : PFacts p) {S : Nat} {σ s : State}
    (hp : (Spec.MlDsa.keyGenContract p AArch64.abi S).pre σ) (h : Top σ s) : Lay S kgR (kgW p) s := by
  sig_pre [Spec.MlDsa.keyGenContract, Spec.MlDsa.keyGenSig, AArch64.abi, VG.AArch64.argRegs] at hp
  obtain ⟨hwf, hrd, hwr, d01, d02, d03, d12, d13, d23, hres, n0, n1, n2, n3⟩ := hp
  obtain ⟨k0, k1, k2, k3⟩ := below_of_resv hres
  have hS : S ≤ σ.sp.toNat := le_of_wfP hwf
  have hsm := hF.small
  have e25 := h.x25; have e26 := h.x26; have e27 := h.x27; have e28 := h.x28
  have mrd : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr => by
    rw [h.rd, h.wr]; exact inR_self hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [h.sp]; exact hS⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl)
    exacts [by decide, hsm.1, hsm.2.1, hsm.2.2]
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) b' (rfl | rfl | rfl | rfl) hne hw <;>
      first
        | exact absurd rfl hne
        | simp only [e25, e26, e27, e28]
          first
            | assumption
            | exact Region.Disjoint.symm (by assumption)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28, h.sp] <;> assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28] <;> assumption
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp only [e25, e26, e27, e28]
    · exact mrd ⟨σ.gpr .x0, 32⟩ (by rw [hrd]; simp)
    · exact mrd ⟨σ.gpr .x3, scrLen p⟩ (by rw [hwr]; simp)
    · exact mrd ⟨σ.gpr .x1, p.pkLen⟩ (by rw [hwr]; simp)
    · exact mrd ⟨σ.gpr .x2, p.skLen⟩ (by rw [hwr]; simp)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl) <;> simp only [e26, e27, e28, h.wr]
    · exact inR_self (r := ⟨σ.gpr .x3, scrLen p⟩) (by rw [hwr]; simp)
    · exact inR_self (r := ⟨σ.gpr .x1, p.pkLen⟩) (by rw [hwr]; simp)
    · exact inR_self (r := ⟨σ.gpr .x2, p.skLen⟩) (by rw [hwr]; simp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl) <;> simp

theorem kgOk (p : Params) : LayOk (kgR ++ kgW p) := by
  intro b hb
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> simp

/-! ## Checks of pointers, by `omega` -/

theorem inB_x25 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x25, o) l = decide (o + l ≤ 32) := rfl
theorem inB_x28 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x28, o) l = decide (o + l ≤ scrLen p) := rfl
theorem inB_x26 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x26, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_x27 (p : Params) (o l : Nat) : inB ((Reg.x25, 32) :: kgW p) (.x27, o) l = decide (o + l ≤ p.skLen) := rfl
theorem inB_x28W (p : Params) (o l : Nat) : inB (kgW p) (.x28, o) l = decide (o + l ≤ scrLen p) := rfl
theorem inB_x26W (p : Params) (o l : Nat) : inB (kgW p) (.x26, o) l = decide (o + l ≤ p.pkLen) := rfl
theorem inB_x27W (p : Params) (o l : Nat) : inB (kgW p) (.x27, o) l = decide (o + l ≤ p.skLen) := rfl

theorem sepB_same (rbs wbs : List (Reg × Nat)) (r : Reg) (o l o' l' : Nat) :
    sepB rbs wbs (r, o) l (r, o') l' =
      (inB (rbs ++ wbs) (r, o) l && inB (rbs ++ wbs) (r, o') l' && (decide (o + l ≤ o') || decide (o' + l' ≤ o))) := by
  simp [sepB]

theorem sepB_kg {p : Params} {r r' : Reg} (h : r ≠ r') (hr : r ∈ [Reg.x25, .x26, .x27, .x28])
    (hr' : r' ∈ [Reg.x25, .x26, .x27, .x28]) (o l o' l' : Nat) :
    sepB kgR (kgW p) (r, o) l (r', o') l' = (inB (kgR ++ kgW p) (r, o) l && inB (kgR ++ kgW p) (r', o') l') := by
  have h1 : (r != r') = true := bne_iff_ne.mpr h
  have h2 : (r == r') = false := beq_eq_false_iff_ne.mpr h
  have h3 : (isW (kgW p) r || isW (kgW p) r') = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr hr'
    rcases hr with rfl | rfl | rfl | rfl <;> rcases hr' with rfl | rfl | rfl | rfl <;> first | exact absurd rfl h | rfl
  simp only [sepB, h1, h2, h3, Bool.false_and, Bool.or_false, Bool.and_true]

/-- Unfolds the checks of pointers into the layout into arithmetic, then
`omega` (in each case of `η`). -/
syntax "lay" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lay) => `(tactic| lay [])
  | `(tactic| lay [$ls,*]) => `(tactic| (
      set_option linter.unusedSimpArgs false in
      simp (config := { decide := true }) only [VG.Proof.MlDsa.AArch64.KeyGen.keepB,
        VG.Proof.MlDsa.AArch64.KeyGen.sepB_same, VG.Proof.MlDsa.AArch64.KeyGen.sepB_kg,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x25, VG.Proof.MlDsa.AArch64.KeyGen.inB_x26,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x27, VG.Proof.MlDsa.AArch64.KeyGen.inB_x28,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x26W, VG.Proof.MlDsa.AArch64.KeyGen.inB_x27W,
        VG.Proof.MlDsa.AArch64.KeyGen.inB_x28W, List.all_cons, List.all_nil, List.cons_append, List.nil_append,
        List.all_append, Bool.and_self,
        Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, Bool.true_and, true_and, and_true,
        ↓reduceIte, Bool.false_eq_true, $ls,*]
      set_option linter.unusedSimpArgs false in
      try simp only [VG.Impl.MlDsa.AArch64.KeyGen.oP, VG.Impl.MlDsa.AArch64.KeyGen.oSA,
        VG.Impl.MlDsa.AArch64.KeyGen.oSB, VG.Impl.MlDsa.AArch64.KeyGen.oHX, VG.Impl.MlDsa.AArch64.KeyGen.oKL,
        VG.Impl.MlDsa.AArch64.KeyGen.oSS, VG.Impl.MlDsa.AArch64.KeyGen.SV, VG.Impl.MlDsa.AArch64.KeyGen.oT0, $ls,*]
      and_intros <;> omega_arith))

end VG.Proof.MlDsa.AArch64.KeyGen
