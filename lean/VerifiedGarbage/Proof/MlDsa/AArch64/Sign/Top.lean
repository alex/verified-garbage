import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Blocks
import VerifiedGarbage.Proof.MlDsa.Sign.Setup

/-!
# ML-DSA signing on AArch64: the function's contract, layout, entry and exit

Untrusted: everything here is checked by Lean. The contract the proof is
written against (`signK`, which the shared contract implies), the layout of
the function's buffers (`sk`, `mu`, `rnd` read, in `x25`, `x26`, `x27`;
`scratch` and `sig` written, in `x28` and `x23`), what holds of the state
throughout (`Top`: the permissions and the stack pointer of entry, the
pointers in their registers, the callee-saved registers it never writes,
and the caller's registers saved in `scratch`), the saves (`pro_ok`), the
return (`epi_ok`), branches on `w24` (`ifOkElse_ok`, `ifOkElse_tr`) and
sequences of pieces indexed by a number (`seqR_ok`, `seqR_tr`).
-/

namespace VG.Proof.MlDsa.AArch64.Sign

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm wp_ldrx in_rd_wr)
open VG.Proof.MlDsa.Sign
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The contract -/

/-- The size of `scratch` in bytes. -/
abbrev scrLen (p : Params) : Nat := 8 * scratchWords p

/-- `vg_mldsa*_sign(sk = x0, mu = x1, rnd = x2, sig = x3, scratch = x4) -> w0`, with `S` bytes of stack
below `sp`, and the leakage `signLeakT`. -/
def signK (p : Params) (S : Nat) : Contract isa where
  pre s :=
    s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩] ∧
    s.wr = [⟨s.gpr .x3, p.sigLen⟩, ⟨s.gpr .x4, scrLen p⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x3, p.sigLen⟩ ∧
    Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x4, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x4, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x3, p.sigLen⟩ ∧ Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x4, scrLen p⟩ ∧
    Region.Disjoint ⟨s.gpr .x3, p.sigLen⟩ ⟨s.gpr .x4, scrLen p⟩ ∧
    (below s.sp S).Disjoint ⟨s.gpr .x0, p.skLen⟩ ∧ (below s.sp S).Disjoint ⟨s.gpr .x1, 64⟩ ∧
    (below s.sp S).Disjoint ⟨s.gpr .x2, 32⟩ ∧ (below s.sp S).Disjoint ⟨s.gpr .x3, p.sigLen⟩ ∧
    (below s.sp S).Disjoint ⟨s.gpr .x4, scrLen p⟩ ∧
    (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64 ∧ (s.gpr .x1).toNat + 64 ≤ 2 ^ 64 ∧ (s.gpr .x2).toNat + 32 ≤ 2 ^ 64 ∧
    (s.gpr .x3).toNat + p.sigLen ≤ 2 ^ 64 ∧ (s.gpr .x4).toNat + scrLen p ≤ 2 ^ 64 ∧
    S ≤ s.sp.toNat
  post s s' :=
    Outcome (fun b => signMu p b (bytesAt s.mem (s.gpr .x0) p.skLen) (bytesAt s.mem (s.gpr .x1) 64)
      (bytesAt s.mem (s.gpr .x2) 32)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x3) p.sigLen)
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp ∧
    signLeakT p (bytesAt s₁.mem (s₁.gpr .x0) p.skLen) (bytesAt s₁.mem (s₁.gpr .x1) 64)
        (bytesAt s₁.mem (s₁.gpr .x2) 32) =
      signLeakT p (bytesAt s₂.mem (s₂.gpr .x0) p.skLen) (bytesAt s₂.mem (s₂.gpr .x1) 64)
        (bytesAt s₂.mem (s₂.gpr .x2) 32)

/-! ## The layout -/

/-- `sk`, `mu` and `rnd`. -/
abbrev sgR (p : Params) : List (Reg × Nat) := [(.x25, p.skLen), (.x26, 64), (.x27, 32)]
/-- `scratch` and `sig`. -/
abbrev sgW (p : Params) : List (Reg × Nat) := [(.x28, scrLen p), (.x23, p.sigLen)]
abbrev sgB (p : Params) : List (Reg × Nat) := sgR p ++ sgW p

/-- The pointers the function keeps, and the registers they arrive in. -/
abbrev sgM : List (Reg × Reg) := [(.x28, .x4), (.x25, .x0), (.x26, .x1), (.x27, .x2), (.x23, .x3)]

theorem sgB_bases (p : Params) : ∀ b ∈ sgB p, b.1 ∈ bases := by
  intro b hb; simp only [sgB, sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
theorem sgM_bases : ∀ m ∈ sgM, m.1 ∈ bases := by decide

/-- The callee-saved registers the function never writes. -/
abbrev untouched : List Reg := [.x19, .x20, .x21, .x22]

theorem untouched_kept : ∀ r ∈ untouched, r ∈ keptRegs := by decide

/-- The register saved at `scratch + 840 + 8k`. -/
abbrev savedReg (k : Nat) : Reg := savedRegs.getD k .x0

/-- What holds throughout the function entered in `σ`. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  regs : ∀ m ∈ sgM, s.gpr m.1 = σ.gpr m.2
  cs : ∀ r ∈ untouched, s.gpr r = σ.gpr r
  saved : ∀ k < 7, s.mem.readW (pa s (sc (oSV + 8 * k))) 64 = σ.gpr (savedReg k)
  vcs : ∀ r ∈ preservedV, (s.v r).extractLsb' 0 64 = (σ.v r).extractLsb' 0 64

section
variable {p : Params} {S : Nat} {σ : State} (hp : (signK p S).pre σ)
include hp

theorem sgLay (hsz : scrLen p < 2 ^ 32 ∧ p.skLen < 2 ^ 32 ∧ p.sigLen < 2 ^ 32) {s : State}
    (h : Top σ s) : Lay S (sgR p) (sgW p) s := by
  obtain ⟨hrd, hwr, d1, d2, d3, d4, d5, d6, d7, k1, k2, k3, k4, k5, n1, n2, n3, n4, n5, hsp⟩ := hp
  have e1 : s.gpr .x28 = σ.gpr .x4 := h.regs (.x28, .x4) (by decide)
  have e2 : s.gpr .x25 = σ.gpr .x0 := h.regs (.x25, .x0) (by decide)
  have e3 : s.gpr .x26 = σ.gpr .x1 := h.regs (.x26, .x1) (by decide)
  have e4 : s.gpr .x27 = σ.gpr .x2 := h.regs (.x27, .x2) (by decide)
  have e5 : s.gpr .x23 = σ.gpr .x3 := h.regs (.x23, .x3) (by decide)
  have mem : ∀ r ∈ σ.rd ++ σ.wr, InRegions (s.rd ++ s.wr) r.base r.len := fun r hr =>
    ⟨r, by rw [h.rd, h.wr]; exact hr, Region.contains_self _ _⟩
  have memw : ∀ r ∈ σ.wr, InRegions s.wr r.base r.len := fun r hr =>
    ⟨r, by rw [h.wr]; exact hr, Region.contains_self _ _⟩
  refine ⟨?_, fun b hb b' hb' hne hw => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_, fun b hb => ?_,
    sgB_bases p, by rw [h.sp]; exact hsp⟩
  · intro b hb
    simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb hb'
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
      simp only [wRegs, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, or_self, ne_eq,
        not_true_eq_false] at hne hw ⊢ <;> simp only [e1, e2, e3, e4, e5]
    all_goals first
      | exact d1 | exact d2 | exact d3 | exact d4 | exact d5 | exact d6 | exact d7
      | exact d1.symm | exact d2.symm | exact d3.symm | exact d4.symm | exact d5.symm | exact d6.symm | exact d7.symm
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5, h.sp]
    exacts [k1, k2, k3, k5, k4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [n1, n2, n3, n5, n4]
  · simp only [sgR, sgW, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp only [e1, e2, e3, e4, e5]
    exacts [mem ⟨σ.gpr .x0, p.skLen⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .x1, 64⟩ (by rw [hrd]; simp),
      mem ⟨σ.gpr .x2, 32⟩ (by rw [hrd]; simp), mem ⟨σ.gpr .x4, scrLen p⟩ (by rw [hwr]; simp),
      mem ⟨σ.gpr .x3, p.sigLen⟩ (by rw [hwr]; simp)]
  · simp only [sgW, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> simp only [e1, e5]
    exacts [memw ⟨σ.gpr .x4, scrLen p⟩ (by rw [hwr]; simp), memw ⟨σ.gpr .x3, p.sigLen⟩ (by rw [hwr]; simp)]

end

/-- The saved registers are apart from the regions `ws`. -/
def topChk (bs : List (Reg × Nat)) (ws : List (Ptr × Nat)) : Bool :=
  (List.range 7).all fun k => keepB bs ws (sc (oSV + 8 * k)) 8

theorem Top.step {S : Nat} {σ s s' : State} {rbs wbs : List (Reg × Nat)} (h : Top σ s)
    (L : Lay S rbs wbs s) {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws)
    (hc : topChk (rbs ++ wbs) ws = true) : Top σ s' := by
  simp only [topChk, List.all_eq_true, List.mem_range] at hc
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp,
    fun m hm => (hP.bs _ (sgM_bases m hm)).trans (h.regs m hm),
    fun r hr => by rw [hP.cs r (untouched_kept r hr), h.cs r hr], fun k hk => ?_,
    fun r hr => (hP.vcs r hr).trans (h.vcs r hr)⟩
  rw [L.keepW hP (hc k hk)]; exact h.saved k hk

/-! ## Saving the registers -/

theorem pro_eq : pro = (List.range 7).map (fun k => .str .x (savedRegs.getD k .x0) .x4 (oSV + 8 * k)) ++
    ([.addImm .x .x28 .x4 0, .addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0, .addImm .x .x27 .x2 0,
      .addImm .x .x23 .x3 0, .movz .x .x24 1 0] : List Instr) := rfl

theorem pro_ok {σ : State} (hin : ∀ k < 7, InRegions σ.wr (σ.gpr .x4 + BitVec.ofNat 64 (oSV + 8 * k)) 8) :
    WP isa (.block pro) σ fun s => Top σ s ∧ s.gpr .x24 = 1 ∧
      Frame [⟨σ.gpr .x4 + BitVec.ofNat 64 oSV, 56⟩] σ.mem s.mem := by
  rw [pro_eq, WP.block_append_iff]
  refine WP.mono (WP.preservedV (Proof.MlKem.AArch64.KeyGen.saves_ok
    (σ.gpr .x4) .x4 oSV savedRegs (by decide) (by decide) 7
    (by decide) rfl hin) (by decide +kernel)) fun s₁ ⟨⟨g₁, r₁, w₁, p₁, z₁, f₁⟩, hv₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ h₂ e₂ => wp_addImm (by decide) fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_addImm (by decide) fun s₅ h₅ e₅ =>
      wp_addImm (by decide) fun s₆ h₆ e₆ => wp_movz fun s₇ h₇ e₇ => wp_nil ?_
  have o : Only [.x28, .x25, .x26, .x27, .x23, .x24] s₁ s₇ :=
    (((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  have e28 : s₇.gpr .x28 = σ.gpr .x4 := by
    rw [h₇.get .x28, h₆.get .x28, h₅.get .x28, h₄.get .x28, h₃.get .x28, e₂, BitVec.add_zero, g₁]
  refine ⟨⟨by rw [o.rd, r₁], by rw [o.wr, w₁], by rw [o.sp, p₁], fun m hm => ?_, fun r hr => ?_, fun k hk => ?_,
    fun r hr => (o.vcs r hr).trans (hv₁ r hr)⟩,
    by rw [e₇]; rfl, by rw [o.mem]; exact f₁⟩
  · simp only [sgM, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · exact e28
    · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, h₄.get .x25, e₃, BitVec.add_zero, h₂.get .x0, g₁]
    · rw [h₇.get .x26, h₆.get .x26, h₅.get .x26, e₄, BitVec.add_zero, h₃.get .x1, h₂.get .x1, g₁]
    · rw [h₇.get .x27, h₆.get .x27, e₅, BitVec.add_zero, h₄.get .x2, h₃.get .x2, h₂.get .x2, g₁]
    · rw [h₇.get .x23, e₆, BitVec.add_zero, h₅.get .x3, h₄.get .x3, h₃.get .x3, h₂.get .x3, g₁]
  · rw [o.get r (by revert r; decide), g₁]
  · rw [o.mem, pa, e28]; exact z₁ k hk

/-! ## The return -/

theorem epi_eq : epi = .addImm .x .x0 .x24 0 :: [.ldr .x .x23 .x28 (oSV + 8 * 0), .ldr .x .x24 .x28 (oSV + 8 * 1),
    .ldr .x .x25 .x28 (oSV + 8 * 2), .ldr .x .x26 .x28 (oSV + 8 * 3), .ldr .x .x27 .x28 (oSV + 8 * 4),
    .ldr .x .x30 .x28 (oSV + 8 * 5), .ldr .x .x28 .x28 (oSV + 8 * 6)] := rfl

theorem epi_ok {σ s : State} (h : Top σ s) (hin : ∀ k < 7, InRegions (s.rd ++ s.wr) (pa s (sc (oSV + 8 * k))) 8) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.gpr .x0 = s.gpr .x24 ∧ s'.mem = s.mem := by
  have ld : ∀ k < 7, ∀ {w : State}, w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = s.gpr .x28 →
      w.gpr .x28 + BitVec.ofNat 64 (oSV + 8 * k) = pa s (sc (oSV + 8 * k)) ∧
      InRegions (w.rd ++ w.wr) (pa s (sc (oSV + 8 * k))) 8 ∧
      w.mem.readW (pa s (sc (oSV + 8 * k))) 64 = σ.gpr (savedReg k) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ => ⟨by rw [h28], by rw [hr, hw]; exact hin k hk', by rw [hm]; exact h.saved k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = s.gpr .x28 →
      w'.rd = s.rd ∧ w'.wr = s.wr ∧ w'.mem = s.mem ∧ w'.gpr .x28 = s.gpr .x28 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  rw [epi_eq]
  refine wp_addImm (by decide) fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, rfl⟩
  have l₁ := ld 0 (by decide) g₁
  refine wp_ldrx (by decide) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 1 (by decide) g₂
  refine wp_ldrx (by decide) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 2 (by decide) g₃
  refine wp_ldrx (by decide) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 3 (by decide) g₄
  refine wp_ldrx (by decide) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 4 (by decide) g₅
  refine wp_ldrx (by decide) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 5 (by decide) g₆
  refine wp_ldrx (by decide) l₆.1 l₆.2.1 fun s₇ h₇ e₇ => ?_
  have g₇ := st h₇ (by decide) g₆
  have l₇ := ld 6 (by decide) g₇
  refine wp_ldrx (by decide) l₇.1 l₇.2.1 fun s₈ h₈ e₈ => wp_nil ?_
  have o₈ : Only [.x0, .x23, .x24, .x25, .x26, .x27, .x30, .x28] s s₈ :=
    (((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₈.sp, h.sp], fun r hr => (o₈.vcs r hr).trans (h.vcs r hr)⟩, ?_, o₈.mem⟩
  · by_cases ho : r ∈ savedRegs
    · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₈.get .x23, h₇.get .x23, h₆.get .x23, h₅.get .x23, h₄.get .x23, h₃.get .x23, e₂]; exact l₁.2.2
      · rw [h₈.get .x24, h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₈.get .x25, h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₈.get .x26, h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₈.get .x27, h₇.get .x27, e₆]; exact l₅.2.2
      · rw [h₈.get .x30, e₇]; exact l₆.2.2
      · rw [e₈]; exact l₇.2.2
    · have hu : r ∈ untouched := by revert r ho hr; decide
      rw [o₈.get r (by revert r hu; decide), h.cs r hu]
  · rw [h₈.get .x0, h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, BitVec.add_zero]

/-! ## Branches on `w24` -/

theorem eval24 (s : State) : isa.eval (.nonzero .w .x24) s = some ((s.gpr .x24).setWidth 32 != 0) := rfl

theorem ifOkElse_ok {t e : Prog isa} {s : State} {Q : State → Prop}
    (ht : (s.gpr .x24).setWidth 32 ≠ 0 → WP isa t s Q) (he : (s.gpr .x24).setWidth 32 = 0 → WP isa e s Q) :
    WP isa (ifOkElse t e) s Q :=
  WP.ite (M := isa) _ (eval24 s) (fun hb => ht (by simpa using hb)) fun hb => he (by simpa using hb)

theorem ifOkElse_tr {t e : Prog isa} {P Q : State → State → Prop}
    (hq : ∀ x y, P x y → (x.gpr .x24).setWidth 32 = (y.gpr .x24).setWidth 32)
    (ht : RelCT isa (fun x y => P x y ∧ (x.gpr .x24).setWidth 32 ≠ 0) t Q)
    (he : RelCT isa (fun x y => P x y ∧ (x.gpr .x24).setWidth 32 = 0) e Q) :
    RelCT isa P (ifOkElse t e) Q :=
  RelCT.ite (fun x y h => by rw [eval24, eval24, hq x y h])
    (RelCT.mono ht (fun x y ⟨h, hc⟩ => ⟨h, by rw [eval24] at hc; simpa using hc⟩) fun _ _ h => h)
    (RelCT.mono he (fun x y ⟨h, hc⟩ => ⟨h, by rw [eval24] at hc; simpa using hc⟩) fun _ _ h => h)

/-! ## Sequences -/

theorem seqR_ok {f : Nat → Prog isa} {I : Nat → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → ∀ s, I k s → WP isa (f k) s (I (k + 1))) →
      ∀ s, I a s → WP isa (seqR f a n) s (I (a + n))
  | 0, a, _, s, hs => WP.block_nil hs
  | n + 1, a, h, s, hs => by
    rw [seqR]
    refine WP.seq (WP.mono (h a (Nat.le_refl _) (by omega) s hs) fun s₁ h₁ => ?_)
    rw [show a + (n + 1) = a + 1 + n by omega]
    exact seqR_ok n (a + 1) (fun k hk hk' => h k (by omega) (by omega)) s₁ h₁

theorem nil_tr {P : State → State → Prop} : RelCT isa P (.block []) P := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  rw [Exec.block_iff] at e₁ e₂
  simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
  obtain ⟨rfl, rfl⟩ := e₁
  obtain ⟨rfl, rfl⟩ := e₂
  exact ⟨rfl, hp⟩

theorem seqR_tr {f : Nat → Prog isa} {R : Nat → State → State → Prop} :
    ∀ (n a : Nat), (∀ k, a ≤ k → k < a + n → RelCT isa (R k) (f k) (R (k + 1))) →
      RelCT isa (R a) (seqR f a n) (R (a + n))
  | 0, _, _ => nil_tr
  | n + 1, a, h => by
    rw [seqR, show a + (n + 1) = a + 1 + n by omega]
    exact RelCT.seq (h a (Nat.le_refl _) (by omega)) (seqR_tr n (a + 1) fun k hk hk' => h k (by omega) (by omega))

end VG.Proof.MlDsa.AArch64.Sign
