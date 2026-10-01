import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Lanes
import VerifiedGarbage.Proof.X25519.X86_64.Iter

/-!
# X25519 on x86-64 with AVX512_IFMA: stage 1 of an iteration

Untrusted: everything here is checked by Lean. From `(x₂, z₂, x₃, z₃)` in
the lanes of `ymm0–ymm4`, stage 1 and its product leave `(AA, BB, DA, CB)`
there.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono contains_sc)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw sel4)

theorem scr_ctx {s : State} {base : Addr} (hs : Scr s base) : Ctx s := fun d hd => by
  rw [hs.rdi]; exact ⟨_, hs.wr, contains_sc hd⟩

theorem vm_gpr {s s' : State} (h : vm s s' = s') : s'.gpr = s.gpr := by rw [← h]; rfl
theorem vm_rd {s s' : State} (h : vm s s' = s') : s'.rd = s.rd := by rw [← h]; rfl
theorem vm_wr {s s' : State} (h : vm s s' = s') : s'.wr = s.wr := by rw [← h]; rfl

theorem scr_of {s s' : State} {base : Addr} (hs : Scr s base) (hg : s'.gpr = s.gpr)
    (hw : s'.wr = s.wr) : Scr s' base := ⟨by rw [hg]; exact hs.rdi, by rw [hw]; exact hs.wr, hs.nowrap⟩

/-- What a part of an iteration keeps. -/
structure Kept (base : Addr) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base 1024 480 s.mem s'.mem

theorem Kept.trans {base : Addr} {s₁ s₂ s₃ : State} (h₁ : Kept base s₁ s₂) (h₂ : Kept base s₂ s₃) :
    Kept base s₁ s₃ :=
  ⟨h₂.gpr.trans h₁.gpr, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr, h₁.mem.trans h₂.mem⟩

theorem Kept.vm {base : Addr} {s s' : State} (h : vm s s' = s') (hm : s'.mem = s.mem) : Kept base s s' :=
  ⟨vm_gpr h, vm_rd h, vm_wr h, by rw [hm]; exact Outside.refl _ _ _ _⟩

/-- Stage 1 and its product. -/
theorem part1_ok {s : State} {base : Addr} {x1 : Nat → Nat} (hs : Scr s base) (hk : Consts s.mem base x1)
    (hy : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61) :
    WP isa (.block (stage1 ++ mul4 OPL)) s fun s' => Kept base s s' ∧
      (∀ l < 4, ∀ i < 5, lanes s' 0 l i < 2 ^ 61) ∧
      fe5 (lanes s' 0 0) = (fe5 (lanes s 0 0) + fe5 (lanes s 0 1)) * (fe5 (lanes s 0 0) + fe5 (lanes s 0 1)) ∧
      fe5 (lanes s' 0 1) = (fe5 (lanes s 0 0) - fe5 (lanes s 0 1)) * (fe5 (lanes s 0 0) - fe5 (lanes s 0 1)) ∧
      fe5 (lanes s' 0 2) = (fe5 (lanes s 0 2) - fe5 (lanes s 0 3)) * (fe5 (lanes s 0 0) + fe5 (lanes s 0 1)) ∧
      fe5 (lanes s' 0 3) = (fe5 (lanes s 0 2) + fe5 (lanes s 0 3)) * (fe5 (lanes s 0 0) - fe5 (lanes s 0 1)) := by
  have hr := hs.rdi
  simp only [stage1, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (s1a_wp hr (scr_ctx hs) hk hy) fun s₁ ⟨v₁, m₁, u₁, _⟩ => ?_
  have hs₁ := scr_of hs (vm_gpr v₁) (vm_wr v₁)
  have hk₁ : Consts s₁.mem base x1 := by rw [m₁]; exact hk
  rw [WP.block_append_iff]
  refine WP.mono (carryI_wp hs₁.rdi (scr_ctx hs₁) hk₁ fun l hl i hi => (u₁ l hl i hi).2) fun s₂ ⟨v₂, m₂, u₂, _⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  rw [WP.block_append_iff]
  refine WP.mono (s1b_wp hs₂.rdi (scr_ctx hs₂)) fun s₃ ⟨g₃, r₃, w₃, o₃, u₃, _⟩ => ?_
  have hs₃ := scr_of hs₂ g₃ w₃
  refine WP.mono (mul4_wp (a := OPL) (by decide) (mulS_eq _ _) (mulL_nat) mulL_ok mulL_keep mulL_st
    hs₃.rdi (scr_ctx hs₃) (fun l hl i hi => by rw [(u₃ l hl i hi).1]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2)
    (fun l hl i hi => by rw [(u₃ l hl i hi).2]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2))
    fun s₄ ⟨v₄, m₄, u₄, _⟩ => ?_
  have K : Kept base s s₄ :=
    (((Kept.vm v₁ m₁).trans (Kept.vm v₂ m₂)).trans ⟨g₃, r₃, w₃, o₃.mono (by decide) (by decide)⟩).trans
      (Kept.vm v₄ m₄)
  -- the values of the lanes
  have fU : ∀ l < 4, fe5 (lanes s₂ 0 l) = fe5 (fun i => sumDiff (lanes s 0) l i) := fun l hl => by
    rw [fe5_congr (fun i hi => (u₂ l hl i hi).1), fe5_carry _ (by have := (u₁ l hl 4 (by decide)).2; omega)]
    exact fe5_congr fun i hi => (u₁ l hl i hi).1
  have hle : ∀ l < 4, ∀ i < 5, lanes s 0 l i ≤ kbv i := fun l hl i hi => by
    have := hy l hl i hi; simp only [kbv]; split <;> omega
  have fA : fe5 (fun i => sumDiff (lanes s 0) 0 i) = fe5 (lanes s 0 0) + fe5 (lanes s 0 1) :=
    fe5_add fun i _ => rfl
  have fB : fe5 (fun i => sumDiff (lanes s 0) 1 i) = fe5 (lanes s 0 0) - fe5 (lanes s 0 1) :=
    fe5_sub (fun i _ => rfl) (hle 1 (by decide))
  have fC : fe5 (fun i => sumDiff (lanes s 0) 2 i) = fe5 (lanes s 0 2) + fe5 (lanes s 0 3) :=
    fe5_add fun i _ => rfl
  have fD : fe5 (fun i => sumDiff (lanes s 0) 3 i) = fe5 (lanes s 0 2) - fe5 (lanes s 0 3) :=
    fe5_sub (fun i _ => rfl) (hle 3 (by decide))
  have fM : ∀ l < 4, fe5 (lanes s₄ 0 l) =
      fe5 (lanes s₂ 0 (sel4 (ord 0 1 3 2).toNat l)) * fe5 (lanes s₂ 0 (sel4 (ord 0 1 0 1).toNat l)) :=
    fun l hl => by
      rw [fe5_congr (fun i hi => (u₄ l hl i hi).1),
        fe5_mul (fun i hi => by rw [(u₃ l hl i hi).1]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2)
          (fun i hi => by rw [(u₃ l hl i hi).2]; exact (u₂ _ (VG.Proof.Poly1305.X86_64.Avx2.sel4_lt _ _) i hi).2),
        fe5_congr (fun i hi => (u₃ l hl i hi).1), fe5_congr (fun i hi => (u₃ l hl i hi).2)]
  refine ⟨K, fun l hl i hi => (u₄ l hl i hi).2, ?_, ?_, ?_, ?_⟩
  · rw [fM 0 (by decide), show sel4 (ord 0 1 3 2).toNat 0 = 0 by decide, show sel4 (ord 0 1 0 1).toNat 0 = 0 by decide,
      fU 0 (by decide), fA]
  · rw [fM 1 (by decide), show sel4 (ord 0 1 3 2).toNat 1 = 1 by decide, show sel4 (ord 0 1 0 1).toNat 1 = 1 by decide,
      fU 1 (by decide), fB]
  · rw [fM 2 (by decide), show sel4 (ord 0 1 3 2).toNat 2 = 3 by decide, show sel4 (ord 0 1 0 1).toNat 2 = 0 by decide,
      fU 3 (by decide), fU 0 (by decide), fD, fA]
  · rw [fM 3 (by decide), show sel4 (ord 0 1 3 2).toNat 3 = 2 by decide, show sel4 (ord 0 1 0 1).toNat 3 = 1 by decide,
      fU 2 (by decide), fU 1 (by decide), fC, fB]

end VG.Proof.X25519.X86_64.Ifma
