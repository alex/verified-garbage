import VerifiedGarbage.Proof.MlKem.AArch64.Barrett

/-!
# ML-KEM on AArch64: what the NTT and its inverse share

Untrusted: everything here is checked by Lean. The per-target contract of
both (`inPlaceAArch64`), the facts that hold throughout (`St`: the
constants, the table of zetas in `scratch`), and a butterfly's effect on the
polynomial in memory, from its two stores (`polyIs_write2`).
-/

namespace VG.Proof.MlKem

open VG VG.AArch64 VG.Spec.MlKem

/-- The contract the proofs are written against (and verified callers use);
the artifacts' are the shared contracts of `Spec/`, which imply it.
AArch64 contract for `f = x0, scratch = x1`: if the polynomial at `f` is
reduced, it becomes `t` of it, reduced. The code may read and write `f` and
`scratch` (1024 bytes), which do not overlap. -/
def inPlaceAArch64 (t : Poly → Poly) : Contract AArch64.isa where
  pre s :=
    s.rd = [] ∧ s.wr = [⟨s.gpr .x0, 1024⟩, ⟨s.gpr .x1, 1024⟩] ∧
    Region.Disjoint ⟨s.gpr .x0, 1024⟩ ⟨s.gpr .x1, 1024⟩ ∧ Reduced s.mem (s.gpr .x0)
  post s s' := PolyIs s'.mem (s.gpr .x0) (t (polyAt s.mem (s.gpr .x0)))
  pub s₁ s₂ := s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.sp = s₂.sp

end VG.Proof.MlKem

namespace VG.Proof.MlKem.AArch64.Ntt

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Spec.MlKem

section
variable (s₀ : State)

abbrev fP : Addr := s₀.gpr .x0
abbrev sP : Addr := s₀.gpr .x1
abbrev P₀ : Poly := polyAt s₀.mem (fP s₀)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [polyRegion (fP s₀), polyRegion (sP s₀)]
  disj : (polyRegion (fP s₀)).Disjoint (polyRegion (sP s₀))
  red : Reduced s₀.mem (fP s₀)

theorem pre_of {t : Poly → Poly} {s₀ : State} (h : (inPlaceAArch64 t).pre s₀) : Pre s₀ :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- What holds throughout. -/
structure St (s₀ : State) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x0 : s.gpr .x0 = fP s₀
  x9 : (s.gpr .x9).toNat = q
  x10 : (s.gpr .x10).toNat = 1290167
  tab : ∀ k < 128, s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32 =
    BitVec.ofNat 32 (zetaTable.getD k 0)

theorem St.keep {s₀ s s' : State} (h : St s₀ s) {rs : List Reg} (hk : Keep rs s s')
    (hm : s'.mem = s.mem) (h0 : Reg.x0 ∉ rs := by decide) (h9 : Reg.x9 ∉ rs := by decide)
    (h10 : Reg.x10 ∉ rs := by decide) : St s₀ s' :=
  ⟨by rw [hk.rd, h.rd], by rw [hk.wr, h.wr], by rw [hk.sp, h.sp], by rw [hk.get .x0 h0, h.x0],
    by rw [hk.get .x9 h9, h.x9], by rw [hk.get .x10 h10, h.x10], fun k hk' => by rw [hm]; exact h.tab k hk'⟩

theorem Pre.in_f {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {i : Nat} (hi : i < 256) :
    InRegions s.wr (coeffAddr (fP s₀) i) 4 := by
  rw [h.wr, hp.wr]
  exact in_regions (List.mem_cons_self ..) (coeff_contains _ (show i < n from hi))

theorem Pre.in_f' {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {i : Nat} (hi : i < 256) :
    InRegions (s.rd ++ s.wr) (coeffAddr (fP s₀) i) 4 := by
  rw [h.rd, hp.rd]; exact hp.in_f h hi

/-- The zeta at `[x12]` for the `k`-th entry of the table. -/
theorem Pre.in_tab {s₀ s : State} (hp : Pre s₀) (h : St s₀ s) {k : Nat} (hk : k < 128) :
    InRegions (s.rd ++ s.wr) (sP s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.rd, h.wr, hp.rd, hp.wr]
  exact in_regions (R := polyRegion (sP s₀)) (by simp) (contains_off (by omega) (by decide))

/-- Storing coefficients `j` and `j'` keeps the table. -/
theorem Pre.tab_write {s₀ : State} (hp : Pre s₀) {m m' : Mem} (hf : Frame [polyRegion (fP s₀)] m m')
    (ht : ∀ k < 128, m.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32 = BitVec.ofNat 32 (zetaTable.getD k 0)) :
    ∀ k < 128, m'.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32 = BitVec.ofNat 32 (zetaTable.getD k 0) :=
  fun k hk => by
    rw [hf.readW (r := polyRegion (sP s₀)) (contains_off (by omega) (by decide)) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.disj.symm) (by decide)]
    exact ht k hk

/-- Two stores into the polynomial at `p`: coefficients `j` and `j'`. -/
theorem polyIs_write2 {m : Mem} {p : Addr} {P R : Poly} (h : PolyIs m p P) {j j' : Nat} (hj : j < 256)
    (hj' : j' < 256) (hne : j ≠ j') {x y : Zq}
    (hR : ∀ i < 256, R[i]! = if i = j then x else if i = j' then y else P[i]!) :
    PolyIs ((m.writeW (coeffAddr p j) (BitVec.ofNat 32 x.val)).writeW (coeffAddr p j')
      (BitVec.ofNat 32 y.val)) p R := by
  refine polyIs_of_coeffAt fun i hi => ?_
  rw [coeffAt_writeW _ _ hi (show j' < n from hj'), coeffAt_writeW _ _ hi (show j < n from hj), hR i hi]
  by_cases e : j = i
  · subst e; rw [ite_eq_right (Ne.symm hne), ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right e, ite_eq_right (Ne.symm e)]
    by_cases e' : j' = i
    · subst e'; rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right e', ite_eq_right (Ne.symm e'), polyIs_coeffAt h hi]

theorem zetaTable_zeta {k : Nat} (hk : k < 128) : zetaTable.getD k 0 = (zeta k).val := by
  rw [zetaTable_eq, zetas_getD hk]

/-- The zeta loaded from the table, as the element of `ℤ_q`. -/
theorem zeta_load {s₀ s : State} (h : St s₀ s) {k : Nat} (hk : k < 128) :
    ((s.mem.readW (sP s₀ + BitVec.ofNat 64 (4 * k)) 32).setWidth 64).toNat = (zeta k).val := by
  rw [toNat_readW32, h.tab k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt
    (by have := zetaTable_lt k hk; have : q = 3329 := rfl; omega), zetaTable_zeta hk]

end VG.Proof.MlKem.AArch64.Ntt
