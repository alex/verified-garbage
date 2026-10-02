import VerifiedGarbage.Proof.MlDsa.X86.Round.Arith
import VerifiedGarbage.Proof.MlKem.X86.Leaf
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-DSA on x86 (32-bit): what the rounding functions share

The arguments of a leaf (`Impl.MlKem.X86.leaf`) after its push (`arg_P0`), the
coefficients of the polynomials at pointers advanced by 4 per iteration
(`ea_cf`), and the coefficients of input polynomials, which the functions
never write (`in_keep`).
-/

namespace VG.Proof.MlDsa.X86.Round

open VG VG.X86 VG.Impl.MlDsa.X86.Round
open VG.Impl.MlKem.X86 (at_)
open VG.Spec.MlDsa (q gamma2s coeffAt Reduced)
open VG.Proof.MlDsa.Round (coeffAddr pR coeff_contains coeffAt_frame n_eq mem_gamma2s)
open VG.Proof.MlKem.X86 (E0 P0 P0_esp P0_wr frameR retR saveRegs_len ea_add toNat_ofNat32)

/-- The stack below the return address, as the contracts state it. -/
abbrev stkR (s₀ : State) : Region := ⟨(E0 s₀).setWidth 64 - 16#64, 16⟩

/-- The pointer argument `i`, as an address. -/
abbrev pA (s₀ : State) (i : Nat) : Addr := (arg s₀ i).setWidth 64

/-- The `n` argument words. -/
abbrev aR (s₀ : State) (n : Nat) : Region := ⟨argAddr s₀ 0, 4 * n⟩

theorem stk_eq {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : stkR s₀ = frameR s₀ := by
  simp only [stkR, frameR, below]; rw [Taint.sub_setWidth h]

/-- The push changes nothing of a region apart from the frame. -/
theorem P0_mem {s₀ : State} (h : 16 ≤ (E0 s₀).toNat) : Frame [frameR s₀] s₀.mem (P0 s₀).mem := by
  have hf := pushed_frame (rs := Impl.MlKem.X86.saveRegs) (s := s₀) (by decide) (by rw [saveRegs_len]; exact h)
  rw [saveRegs_len] at hf
  exact hf

theorem arg_contains {s₀ : State} {n i : Nat} (hi : i < n) (hfit : (E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32) :
    (aR s₀ n).Contains (argAddr s₀ i) 4 := by
  simp only [argAddr, Region.Contains, E0] at hfit ⊢
  bv_omega

/-- Argument `i` of `n`, after the leaf's push: its address `[esp + 20 + 4i]`, and its value. -/
theorem arg_P0 {s₀ : State} {n i : Nat} (hi : i < n) (hsp : 16 ≤ (E0 s₀).toNat)
    (hfit : (E0 s₀).toNat + 4 + 4 * n ≤ 2 ^ 32) (hin : aR s₀ n ∈ s₀.rd ++ s₀.wr)
    (hstk : (stkR s₀).Disjoint (aR s₀ n)) :
    ((P0 s₀).gpr .esp + BitVec.ofNat 32 (20 + 4 * i)).setWidth 64 = argAddr s₀ i ∧
      InRegions ((P0 s₀).rd ++ (P0 s₀).wr) (argAddr s₀ i) 4 ∧
      (P0 s₀).mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hc := arg_contains hi hfit
  refine ⟨?_, ⟨aR s₀ n, ?_, hc⟩, ?_⟩
  · rw [P0_esp]; simp only [argAddr, E0]; congr 1; bv_omega
  · rw [pushed_rd, P0_wr]
    rcases List.mem_append.mp hin with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  · exact (P0_mem hsp).readW hc (by simpa [← stk_eq hsp] using hstk.symm) (by decide)

/-- Coefficient `k` at the pointer `x + 4k`. -/
theorem ea_cf {x : BitVec 32} (hx : x.toNat + 1024 ≤ 2 ^ 32) {k : Nat} (hk : k < 256) :
    (x + BitVec.ofNat 32 (4 * k) + BitVec.ofNat 32 0).setWidth 64 = coeffAddr (x.setWidth 64) k := by
  rw [ea_add (by omega), Nat.add_zero]

/-- A polynomial apart from the frame and the regions written keeps its coefficients. -/
theorem in_keep {s₀ : State} {W : List Region} {m : Mem} (hsp : 16 ≤ (E0 s₀).toNat)
    (hf : Frame W (P0 s₀).mem m) {p : Addr} (hstk : (stkR s₀).Disjoint (pR p))
    (hw : ∀ r ∈ W, (pR p).Disjoint r) {k : Nat} (hk : k < 256) :
    coeffAt m p k = coeffAt s₀.mem p k := by
  rw [coeffAt_frame hf hw (by rw [n_eq]; exact hk), coeffAt_frame (P0_mem hsp) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [← stk_eq hsp]; exact hstk.symm) (by rw [n_eq]; exact hk)]

theorem inRd {s : State} {a : Addr} (h : InRegions s.wr a 4) : InRegions (s.rd ++ s.wr) a 4 :=
  let ⟨r, hr, c⟩ := h; ⟨r, List.mem_append_right _ hr, c⟩

/-- `x - k` is zero exactly when `x = k`. -/
theorem sub_beq_zero' (x k : BitVec 32) : (x - k == 0) = (x == k) := by
  by_cases h : x = k
  · subst h; simp
  · have : x - k ≠ 0 := fun e => h (by bv_omega)
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem gamma_cases {g : BitVec 32} (hg : g.toNat ∈ gamma2s) :
    (g == BitVec.ofNat 32 g32) = true ∧ g.toNat = g32 ∨ (g == BitVec.ofNat 32 g32) = false ∧ g.toNat = g88 := by
  rcases mem_gamma2s hg with e | e
  · refine .inr ⟨?_, e⟩
    rw [beq_eq_false_iff_ne]; intro h; rw [h] at e; exact absurd e (by decide)
  · refine .inl ⟨?_, e⟩
    rw [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (e.trans rfl)

theorem g32_mem : g32 ∈ gamma2s := by decide
theorem g88_mem : g88 ∈ gamma2s := by decide

end VG.Proof.MlDsa.X86.Round
