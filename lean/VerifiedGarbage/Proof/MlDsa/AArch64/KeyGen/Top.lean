import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.KgA

/-!
# ML-DSA on AArch64: entry and exit

Untrusted: everything here is checked by Lean. What the top-level functions
keep from their entry state `σ` on (`Top`): the permissions and the stack
pointer, their four arguments in `x25`–`x28`, the callee-saved registers
they never write, and their caller's `x24`–`x28` and `x30` saved in
`scratch`. The prologue establishes it (`pro_ok`), every piece keeps it
(`Top.step`), and the epilogue restores the caller's registers from it
(`epi_ok`).
-/

namespace VG.Proof.MlDsa.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_movz wp_addImm wp_ldrx in_rd_wr)
open VG.Spec.Sha3 (bytesAt)

/-- The callee-saved registers the functions never write. -/
abbrev untouched : List Reg := [.x19, .x20, .x21, .x22, .x23]

/-- What the functions keep from their entry state `σ` on. -/
structure Top (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x25 : s.gpr .x25 = σ.gpr .x0
  x26 : s.gpr .x26 = σ.gpr .x1
  x27 : s.gpr .x27 = σ.gpr .x2
  x28 : s.gpr .x28 = σ.gpr .x3
  cs : ∀ r ∈ untouched, s.gpr r = σ.gpr r
  saved : ∀ k < 6, s.mem.readW (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 64 = σ.gpr (savedRegs.getD k .x0)

theorem untouched_kept : ∀ r ∈ untouched, r ∈ keptRegs := by decide

/-- The saved registers, in `scratch`. -/
abbrev svP : Ptr := sc SV

/-- `Top` is kept by a piece that keeps the saved registers. -/
theorem Top.step {S : Nat} {rbs wbs : List (Reg × Nat)} {σ s s' : State} (h : Top σ s) (L : Lay S rbs wbs s)
    {ws : List (Ptr × Nat)} (hP : PPostB S s s' ws) (hc : keepB rbs wbs ws svP 48 = true) : Top σ s' := by
  have hsv : ∀ k < 6, s'.mem.readW (pa s' svP + BitVec.ofNat 64 (8 * k)) 64 =
      s.mem.readW (pa s svP + BitVec.ofNat 64 (8 * k)) 64 := fun k hk => by
    rw [hP.pa (keepB_bs hc)]
    obtain ⟨n, hn, hl⟩ := inB_spec (keepB_in hc)
    refine hP.frame.readW (r := ⟨pa s svP, 48⟩) (Offset.contains_base _ (by omega) (by omega))
      (L.fdisj hc) (by decide)
  refine ⟨hP.rd.trans h.rd, hP.wr.trans h.wr, hP.sp.trans h.sp, by rw [hP.bs _ (by decide), h.x25],
    by rw [hP.bs _ (by decide), h.x26], by rw [hP.bs _ (by decide), h.x27], by rw [hP.bs _ (by decide), h.x28],
    fun r hr => by rw [hP.cs r (untouched_kept r hr), h.cs r hr], fun k hk => ?_⟩
  have e : σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = pa s svP + BitVec.ofNat 64 (8 * k) := by
    rw [pa, h.x28, BitVec.add_assoc, ← BitVec.ofNat_add]
  have e' : σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = pa s' svP + BitVec.ofNat 64 (8 * k) := by
    rw [pa, hP.bs _ (by decide), h.x28, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [e', hsv k hk, ← e, h.saved k hk]

/-! ## The prologue -/

theorem pro_eq : pro = (List.range 6).map (fun k => .str .x (savedRegs.getD k .x0) .x3 (SV + 8 * k)) ++
    ([.addImm .x .x25 .x0 0, .addImm .x .x26 .x1 0, .addImm .x .x27 .x2 0, .addImm .x .x28 .x3 0,
      .movz .x .x24 1 0] : List Instr) := rfl

theorem pro_ok {σ : State} (hin : ∀ k < 6, InRegions σ.wr (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8) :
    WP isa (.block pro) σ fun s => Top σ s ∧ s.gpr .x24 = 1 ∧
      Frame [⟨σ.gpr .x3 + BitVec.ofNat 64 SV, 48⟩] σ.mem s.mem := by
  rw [pro_eq, WP.block_append_iff]
  refine WP.mono (Proof.MlKem.AArch64.KeyGen.saves_ok (σ.gpr .x3) .x3 SV savedRegs (by decide) (by decide) 6
    (by decide) rfl hin) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
  refine wp_addImm (by decide) fun s₂ h₂ e₂ => wp_addImm (by decide) fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_addImm (by decide) fun s₅ h₅ e₅ => wp_movz fun s₆ h₆ e₆ => wp_nil ?_
  have o : Only [.x25, .x26, .x27, .x28, .x24] s₁ s₆ := ((((h₂.trans h₃).trans h₄).trans h₅).trans h₆).mono
  refine ⟨⟨by rw [o.rd, r₁], by rw [o.wr, w₁], by rw [o.sp, p₁], ?_, ?_, ?_, ?_, fun r hr => ?_, fun k hk => ?_⟩,
    by rw [e₆]; rfl, by rw [o.mem]; exact f₁⟩
  · rw [h₆.get .x25, h₅.get .x25, h₄.get .x25, h₃.get .x25, e₂, BitVec.add_zero, g₁]
  · rw [h₆.get .x26, h₅.get .x26, h₄.get .x26, e₃, BitVec.add_zero, h₂.get .x1, g₁]
  · rw [h₆.get .x27, h₅.get .x27, e₄, BitVec.add_zero, h₃.get .x2, h₂.get .x2, g₁]
  · rw [h₆.get .x28, e₅, BitVec.add_zero, h₄.get .x3, h₃.get .x3, h₂.get .x3, g₁]
  · rw [o.get r (by revert r; decide), g₁]
  · rw [o.mem]; exact z₁ k hk

/-! ## The epilogue -/

theorem epi_ok {σ s : State} (h : Top σ s) (hin : InRegions (s.rd ++ s.wr) (σ.gpr .x3 + BitVec.ofNat 64 SV) 48) :
    WP isa (.block epi) s fun s' => abiPreserved σ s' ∧ s'.gpr .x0 = s.gpr .x24 ∧ s'.mem = s.mem := by
  have ld : ∀ k < 6, ∀ {w : State}, w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = σ.gpr .x3 →
      w.gpr .x28 + BitVec.ofNat 64 (SV + 8 * k) = σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) ∧
      InRegions (w.rd ++ w.wr) (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 8 ∧
      w.mem.readW (σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k)) 64 = σ.gpr (savedRegs.getD k .x0) :=
    fun k hk' {w} ⟨hr, hw, hm, h28⟩ =>
      ⟨by rw [h28], by
        rw [hr, hw, show σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * k) = σ.gpr .x3 + BitVec.ofNat 64 SV +
          BitVec.ofNat 64 (8 * k) by rw [BitVec.add_assoc, ← BitVec.ofNat_add]]
        exact inRegions_sub hin (by omega) (by decide), by rw [hm]; exact h.saved k hk'⟩
  have st : ∀ {w w' : State} {r : Reg}, Only [r] w w' → r ≠ .x28 →
      w.rd = s.rd ∧ w.wr = s.wr ∧ w.mem = s.mem ∧ w.gpr .x28 = σ.gpr .x3 →
      w'.rd = s.rd ∧ w'.wr = s.wr ∧ w'.mem = s.mem ∧ w'.gpr .x28 = σ.gpr .x3 :=
    fun h hr ⟨a, b, c, d⟩ => ⟨by rw [h.rd, a], by rw [h.wr, b], by rw [h.mem, c],
      by rw [h.get .x28 (by simpa using Ne.symm hr), d]⟩
  refine wp_addImm (by decide) fun s₁ h₁ e₁ => ?_
  have g₁ := st h₁ (by decide) ⟨rfl, rfl, rfl, h.x28⟩
  have l₁ := ld 5 (by decide) g₁
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 5)) (by decide) l₁.1 l₁.2.1 fun s₂ h₂ e₂ => ?_
  have g₂ := st h₂ (by decide) g₁
  have l₂ := ld 0 (by decide) g₂
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 0)) (by decide) l₂.1 l₂.2.1 fun s₃ h₃ e₃ => ?_
  have g₃ := st h₃ (by decide) g₂
  have l₃ := ld 1 (by decide) g₃
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 1)) (by decide) l₃.1 l₃.2.1 fun s₄ h₄ e₄ => ?_
  have g₄ := st h₄ (by decide) g₃
  have l₄ := ld 2 (by decide) g₄
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 2)) (by decide) l₄.1 l₄.2.1 fun s₅ h₅ e₅ => ?_
  have g₅ := st h₅ (by decide) g₄
  have l₅ := ld 3 (by decide) g₅
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 3)) (by decide) l₅.1 l₅.2.1 fun s₆ h₆ e₆ => ?_
  have g₆ := st h₆ (by decide) g₅
  have l₆ := ld 4 (by decide) g₆
  refine wp_ldrx (a := σ.gpr .x3 + BitVec.ofNat 64 (SV + 8 * 4)) (by decide) l₆.1 l₆.2.1 fun s₇ h₇ e₇ =>
    wp_nil ?_
  have o₇ : Only [.x0, .x30, .x24, .x25, .x26, .x27, .x28] s s₇ :=
    ((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).mono
  refine ⟨⟨fun r hr => ?_, by rw [o₇.sp, h.sp]⟩, ?_, o₇.mem⟩
  · by_cases ho : r ∈ savedRegs
    · simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h₇.get .x24, h₆.get .x24, h₅.get .x24, h₄.get .x24, e₃]; exact l₂.2.2
      · rw [h₇.get .x25, h₆.get .x25, h₅.get .x25, e₄]; exact l₃.2.2
      · rw [h₇.get .x26, h₆.get .x26, e₅]; exact l₄.2.2
      · rw [h₇.get .x27, e₆]; exact l₅.2.2
      · rw [e₇]; exact l₆.2.2
      · rw [h₇.get .x30, h₆.get .x30, h₅.get .x30, h₄.get .x30, h₃.get .x30, e₂]; exact l₁.2.2
    · have hu : r ∈ untouched := by revert r ho hr; decide
      rw [o₇.get r (by revert r hu; decide), h.cs r hu]
  · rw [h₇.get .x0, h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, BitVec.add_zero]

end VG.Proof.MlDsa.AArch64.KeyGen
