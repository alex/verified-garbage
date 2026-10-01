import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.Block
import VerifiedGarbage.Proof.Ed25519.Group.Double

/-!
# Ed25519 doublings with AVX512_IFMA: a doubling in the lanes

Untrusted: everything here is checked by Lean. `vdbl` leaves in the lanes
of `ymm0–ymm4` the point `dblPoint` of the one there, as field elements
(`fe5`).
-/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64.Ifma VG.Proof.Ed25519
open VG.Impl.X25519.X86_64.Ifma (KM K19 KB0 KB1 OPL OPV kb ord mul4 carry)
open VG.Proof.X25519.X86_64.Ifma (lanes slotv CConsts carryNat fe5 fe5_congr fe5_add fe5_sub fe5_carry
  fe5_mul carryI_wp carryF_wp mul4_wp mulL mulV mulS_eq mulL_nat mulL_ok mulL_keep mulL_st mulV_nat mulV_ok
  mulV_keep mulV_st kbv vm vm_gpr vm_rd vm_wr)
open VG.Proof.X25519.X86_64 (Outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4 sel4_lt)

/-- The point in the lanes of `ymm0–ymm4`. -/
def lanePt (s : State) : Spec.Ed25519.Point :=
  ⟨fe5 (lanes s 0 0), fe5 (lanes s 0 1), fe5 (lanes s 0 2), fe5 (lanes s 0 3)⟩

/-- Limbs below `2⁶¹`, in every lane. -/
def Small (s : State) : Prop := ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61

theorem kbv_ge (i : Nat) : 2 ^ 61 ≤ kbv i := by
  simp only [kbv]; split <;> omega

theorem fe_add_sub (a b c : Spec.X25519.Fe) : a + (b - c) = a - (c - b) :=
  toZ_inj.1 (by rw [toZ_add, toZ_sub, toZ_sub, toZ_sub]; ring)

/-- `(E, G, F, E)` and `(F, H, G, H)` as field elements, from `(A, B, C', P)`. -/
theorem ops_fe (x : Nat → Nat → Nat) (hx : ∀ l < 4, ∀ i < 5, x l i < 2 ^ 52) :
    fe5 (op1 x 0) = fe5 (x 3) + fe5 (x 3) ∧ fe5 (op1 x 1) = fe5 (x 1) - fe5 (x 0) ∧
    fe5 (op1 x 2) = fe5 (x 2) + fe5 (x 2) - (fe5 (x 1) - fe5 (x 0)) ∧
    fe5 (op1 x 3) = fe5 (x 3) + fe5 (x 3) ∧
    fe5 (op2 x 0) = fe5 (x 2) + fe5 (x 2) - (fe5 (x 1) - fe5 (x 0)) ∧
    fe5 (op2 x 1) = fe5 (x 0) + fe5 (x 1) ∧ fe5 (op2 x 2) = fe5 (x 1) - fe5 (x 0) ∧
    fe5 (op2 x 3) = fe5 (x 0) + fe5 (x 1) := by
  have g : fe5 (fun i => kbv i + x 1 i - x 0 i) = fe5 (x 1) - fe5 (x 0) :=
    fe5_sub (fun i hi => by have := hx 0 (by decide) i hi; have := kbv_ge i; omega)
      (fun i hi => by have := hx 0 (by decide) i hi; have := kbv_ge i; omega)
  have f : fe5 (fv x) = fe5 (x 2) + fe5 (x 2) - (fe5 (x 1) - fe5 (x 0)) := by
    rw [fe5_add (z := fv x) (x := fun i => x 2 i + x 2 i) (y := fun i => kbv i + x 0 i - x 1 i)
      (fun i _ => rfl),
      fe5_add (z := fun i => x 2 i + x 2 i) (x := x 2) (y := x 2) (fun i _ => rfl),
      fe5_sub (z := fun i => kbv i + x 0 i - x 1 i) (x := x 0) (y := x 1) (fun i hi => by have := hx 1 (by decide) i hi; have := kbv_ge i; omega)
        (fun i hi => by have := hx 1 (by decide) i hi; have := kbv_ge i; omega), fe_add_sub]
  have e : fe5 (fun i => x 3 i + x 3 i) = fe5 (x 3) + fe5 (x 3) := fe5_add fun _ _ => rfl
  have h : fe5 (fun i => x 0 i + x 1 i) = fe5 (x 0) + fe5 (x 1) := fe5_add fun _ _ => rfl
  exact ⟨e, g, f, e, f, h, g, h⟩

theorem lanes_keep {s t : State} {r : Nat} (hr : r + 5 ≤ 16)
    (h : ∀ q < 16, r ≤ q → q < r + 5 → ∀ l < 4, qw t (xr q) l = qw s (xr q) l) :
    ∀ l < 4, ∀ i < 5, lanes t r l i = lanes s r l i := fun l hl i hi => by
  simp only [lanes]; rw [h (r + i) (by omega) (by omega) (by omega) l hl]

/-- `vdbl`: the lanes doubled, with `T`. -/
theorem vdbl_wp {s : State} {base : Addr} (hs : s.gpr .rdi = base) (hc : VG.Proof.X25519.X86_64.Ifma.Ctx s)
    (hk : EConsts s.mem base) (hx : Small s) :
    WP isa (.block vdbl) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Outside base 1024 320 s.mem s'.mem ∧ Small s' ∧ lanePt s' = dblPoint (lanePt s) := by
  have hcc : CConsts s.mem base := hk.toCConsts
  simp only [vdbl, List.append_assoc]
  -- the point carried
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs hc hcc fun l hl i hi => by have := hx l hl i hi; omega)
    fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ : s₁.gpr .rdi = base := by rw [vm_gpr v₁]; exact hs
  have hc₁ : VG.Proof.X25519.X86_64.Ifma.Ctx s₁ := by
    intro d hd; rw [vm_gpr v₁, vm_wr v₁]; exact hc d hd
  have p₁ : ∀ l < 4, fe5 (lanes s₁ 0 l) = fe5 (lanes s 0 l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₁ l hl i hi).1), fe5_carry _ (by have := hx l hl 4 (by decide); omega)]
  -- the first operands
  rw [WP.block_append_iff]
  refine WP.mono (dblA_wp hs₁ hc₁) fun s₂ ⟨g₂, rd₂, wr₂, o₂, u₂, k₂⟩ => ?_
  have hs₂ : s₂.gpr .rdi = base := by rw [g₂]; exact hs₁
  have hc₂ : VG.Proof.X25519.X86_64.Ifma.Ctx s₂ := by intro d hd; rw [g₂, wr₂]; exact hc₁ d hd
  -- the first product: `(A, B, C', P)`
  rw [WP.block_append_iff]
  refine WP.mono (mul4_wp (by decide) (mulS_eq OPL _) (mulL_nat) mulL_ok mulL_keep mulL_st hs₂ hc₂
    (fun l hl i hi => by rw [(u₂ l hl i hi).1]; exact (u₁ _ (sel4_lt _ _) i hi).2)
    (fun l hl i hi => by rw [(u₂ l hl i hi).2]; exact (u₁ _ (sel4_lt _ _) i hi).2))
    fun s₃ ⟨v₃, m₃, u₃, _⟩ => ?_
  have p₃ : ∀ l < 4, fe5 (lanes s₃ 0 l) =
      fe5 (lanes s 0 (sel4 (ord 0 1 2 0).toNat l)) * fe5 (lanes s 0 (sel4 (ord 0 1 2 1).toNat l)) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₃ l hl i hi).1),
        fe5_mul (fun i hi => by rw [(u₂ l hl i hi).1]; exact (u₁ _ (sel4_lt _ _) i hi).2)
          (fun i hi => by rw [(u₂ l hl i hi).2]; exact (u₁ _ (sel4_lt _ _) i hi).2),
        ← p₁ _ (sel4_lt _ _), ← p₁ _ (sel4_lt _ _)]
      exact congrArg₂ (· * ·) (fe5_congr fun i hi => (u₂ l hl i hi).1)
        (fe5_congr fun i hi => (u₂ l hl i hi).2)
  have hs₃ : s₃.gpr .rdi = base := by rw [vm_gpr v₃]; exact hs₂
  have hc₃ : VG.Proof.X25519.X86_64.Ifma.Ctx s₃ := by intro d hd; rw [vm_gpr v₃, vm_wr v₃]; exact hc₂ d hd
  have mo₃ : Outside base 1024 320 s.mem s₃.mem := by
    rw [m₃, ← m₁]; exact o₂.mono (by decide) (by decide)
  have hk₃ : EConsts s₃.mem base := hk.outside mo₃
  -- carried
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₃ hc₃ hk₃.toCConsts fun l hl i hi => by have := (u₃ l hl i hi).2; omega)
    fun s₄ ⟨v₄, m₄, u₄, _⟩ => ?_
  have p₄ : ∀ l < 4, fe5 (lanes s₄ 0 l) = fe5 (lanes s₃ 0 l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₄ l hl i hi).1), fe5_carry _ (by have := (u₃ l hl 4 (by decide)).2; omega)]
  have hs₄ : s₄.gpr .rdi = base := by rw [vm_gpr v₄]; exact hs₃
  have hc₄ : VG.Proof.X25519.X86_64.Ifma.Ctx s₄ := by intro d hd; rw [vm_gpr v₄, vm_wr v₄]; exact hc₃ d hd
  have hk₄ : EConsts s₄.mem base := by rw [m₄]; exact hk₃
  -- the second operands
  rw [WP.block_append_iff]
  refine WP.mono (dblB_wp hs₄ hc₄ hk₄.toCConsts fun l hl i hi => (u₄ l hl i hi).2)
    fun s₅ ⟨v₅, m₅, u₅, k₅⟩ => ?_
  have hs₅ : s₅.gpr .rdi = base := by rw [vm_gpr v₅]; exact hs₄
  have hc₅ : VG.Proof.X25519.X86_64.Ifma.Ctx s₅ := by intro d hd; rw [vm_gpr v₅, vm_wr v₅]; exact hc₄ d hd
  have hk₅ : EConsts s₅.mem base := by rw [m₅]; exact hk₄
  rw [WP.block_append_iff]
  refine WP.mono (carryF_wp hs₅ hc₅ hk₅.toCConsts fun l hl i hi => (u₅ l hl i hi).2.2.2)
    fun s₆ ⟨v₆, m₆, u₆, k₆⟩ => ?_
  have hs₆ : s₆.gpr .rdi = base := by rw [vm_gpr v₆]; exact hs₅
  have hc₆ : VG.Proof.X25519.X86_64.Ifma.Ctx s₆ := by intro d hd; rw [vm_gpr v₆, vm_wr v₆]; exact hc₅ d hd
  have hk₆ : EConsts s₆.mem base := by rw [m₆]; exact hk₅
  have l₆ := lanes_keep (r := 0) (s := s₅) (t := s₆) (by decide) fun q hq h1 h2 l hl =>
    k₆ q hq (by omega) (by omega) l hl
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₆ hc₆ hk₆.toCConsts fun l hl i hi => by
      rw [l₆ l hl i hi]; exact (u₅ l hl i hi).2.1) fun s₇ ⟨v₇, m₇, u₇, k₇⟩ => ?_
  have hs₇ : s₇.gpr .rdi = base := by rw [vm_gpr v₇]; exact hs₆
  have hc₇ : VG.Proof.X25519.X86_64.Ifma.Ctx s₇ := by intro d hd; rw [vm_gpr v₇, vm_wr v₇]; exact hc₆ d hd
  have l₇ := lanes_keep (r := 5) (s := s₆) (t := s₇) (by decide) fun q hq h1 h2 l hl =>
    k₇ q hq (by omega) (by omega) l hl
  -- the first operand to `OPV`
  rw [WP.block_append_iff]
  refine WP.mono (dblC_wp hs₇ hc₇) fun s₈ ⟨v₈, o₈, u₈, k₈⟩ => ?_
  have hs₈ : s₈.gpr .rdi = base := by rw [vm_gpr v₈]; exact hs₇
  have hc₈ : VG.Proof.X25519.X86_64.Ifma.Ctx s₈ := by intro d hd; rw [vm_gpr v₈, vm_wr v₈]; exact hc₇ d hd
  have l₈ := lanes_keep (r := 5) (s := s₇) (t := s₈) (by decide) fun q hq _ _ l hl => k₈ q hq l hl
  -- the second product
  refine WP.mono (mul4_wp (by decide) (mulS_eq OPV _) (mulV_nat) mulV_ok mulV_keep mulV_st hs₈ hc₈
    (fun l hl i hi => by rw [u₈ l hl i hi]; exact (u₇ l hl i hi).2)
    (fun l hl i hi => by rw [l₈ l hl i hi, l₇ l hl i hi]; exact (u₆ l hl i hi).2))
    fun s₉ ⟨v₉, m₉, u₉, _⟩ => ?_
  refine ⟨by rw [vm_gpr v₉, vm_gpr v₈, vm_gpr v₇, vm_gpr v₆, vm_gpr v₅, vm_gpr v₄, vm_gpr v₃, g₂, vm_gpr v₁],
    by rw [vm_rd v₉, vm_rd v₈, vm_rd v₇, vm_rd v₆, vm_rd v₅, vm_rd v₄, vm_rd v₃, rd₂, vm_rd v₁],
    by rw [vm_wr v₉, vm_wr v₈, vm_wr v₇, vm_wr v₆, vm_wr v₅, vm_wr v₄, vm_wr v₃, wr₂, vm_wr v₁], ?_,
    fun l hl i hi => (u₉ l hl i hi).2, ?_⟩
  · rw [m₇, m₆, m₅, m₄] at o₈
    rw [m₉]; exact mo₃.trans (o₈.mono (by decide) (by decide))
  have p₉ : ∀ l < 4, fe5 (lanes s₉ 0 l) = fe5 (op1 (lanes s₄ 0) l) * fe5 (op2 (lanes s₄ 0) l) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₉ l hl i hi).1),
      fe5_mul (fun i hi => by rw [u₈ l hl i hi]; exact (u₇ l hl i hi).2)
        (fun i hi => by rw [l₈ l hl i hi, l₇ l hl i hi]; exact (u₆ l hl i hi).2),
      fe5_congr (fun i hi => u₈ l hl i hi), fe5_congr (fun i hi => (u₇ l hl i hi).1),
      fe5_carry _ (by rw [l₆ l hl 4 (by decide)]; have := (u₅ l hl 4 (by decide)).2.1; omega),
      fe5_congr (fun i hi => (l₆ l hl i hi).trans (u₅ l hl i hi).1),
      fe5_congr (fun i hi => (l₈ l hl i hi).trans (l₇ l hl i hi)),
      fe5_congr (fun i hi => (u₆ l hl i hi).1),
      fe5_carry _ (by have := (u₅ l hl 4 (by decide)).2.2.2; omega),
      fe5_congr (fun i hi => (u₅ l hl i hi).2.2.1)]
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3⟩ := ops_fe (lanes s₄ 0) (fun l hl i hi => (u₄ l hl i hi).2)
  have hA : fe5 (lanes s₄ 0 0) = fe5 (lanes s 0 0) * fe5 (lanes s 0 0) := by
    rw [p₄ 0 (by decide), p₃ 0 (by decide)]; rfl
  have hB : fe5 (lanes s₄ 0 1) = fe5 (lanes s 0 1) * fe5 (lanes s 0 1) := by
    rw [p₄ 1 (by decide), p₃ 1 (by decide)]; rfl
  have hC : fe5 (lanes s₄ 0 2) = fe5 (lanes s 0 2) * fe5 (lanes s 0 2) := by
    rw [p₄ 2 (by decide), p₃ 2 (by decide)]; rfl
  have hP : fe5 (lanes s₄ 0 3) = fe5 (lanes s 0 0) * fe5 (lanes s 0 1) := by
    rw [p₄ 3 (by decide), p₃ 3 (by decide)]; rfl
  simp only [lanePt, dblPoint]
  rw [p₉ 0 (by decide), p₉ 1 (by decide), p₉ 2 (by decide), p₉ 3 (by decide), a0, a1, a2, a3, b0, b1, b2, b3,
    hA, hB, hC, hP]

end VG.Proof.Ed25519.X86_64.Ifma
