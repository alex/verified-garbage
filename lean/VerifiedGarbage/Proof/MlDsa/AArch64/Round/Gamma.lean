import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith

/-!
# ML-DSA on AArch64: the functions with `γ₂`

Untrusted: everything here is checked by Lean. `vg_mldsa_high_bits`,
`vg_mldsa_low_bits`, `vg_mldsa_make_hint` and `vg_mldsa_use_hint` branch on
`γ₂` (`onGamma`), and each arm puts constants in registers (`consts g`),
then runs the loop of its body. `gamma_ok` proves this once, from what the
constants are (`cv g`) and a body proven for the loop (`loop_ok`), for the
state once `γ₂` is zero-extended.
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa (q gamma2s)

/-- The body of a loop with the constants `cv g` in the registers `fixed`. -/
def GBody (s₁ : State) (ptrs fixed outs clob : List Reg) (cnt : Reg) (cv : Nat → Reg → BitVec 64)
    (V : Nat → Reg → Nat → BitVec 32) (J : Nat → Nat → State → Prop) (ins : List Reg)
    (body : Nat → List Instr) : Prop :=
  ∀ g, IsG g → ∀ sL, Layout sL ins outs → (∀ r ∈ fixed, sL.gpr r = cv g r) → sL.mem = s₁.mem →
    (∀ p ∈ ins ++ outs, sL.gpr p = s₁.gpr p) → ∀ i < 256, ∀ s,
    Inv sL ptrs fixed outs (V g) (J g) i s →
    WP isa (.block (body g ++ ptrs.map (fun p => .addImm .x p p 4) ++ [.subImm .x cnt cnt 1])) s fun s' =>
      (s'.mem = writes s.mem (outs.map fun o => (s.gpr o, V g o i)) ∧
        (∀ p ∈ ptrs, s'.gpr p = s.gpr p + BitVec.ofNat 64 4) ∧
        s'.gpr cnt = s.gpr cnt - BitVec.ofNat 64 1 ∧ J g (i + 1) s') ∧
      Keep clob s s'

theorem gamma_ok {s₁ : State} {gr t cnt : Reg} {ins outs ptrs fixed kc clob : List Reg}
    {consts body : Nat → List Instr} {cv : Nat → Reg → BitVec 64}
    {V : Nat → Reg → Nat → BitVec 32} {J : Nat → Nat → State → Prop}
    (hg : IsG (s₁.gpr gr).toNat) (hL : Layout s₁ ins outs) (htg : t ≠ gr)
    (hptr : ∀ p ∈ ins ++ outs, p ≠ t ∧ p ∉ kc)
    (hout : ∀ o ∈ outs, o ∈ ptrs) (hfix : ∀ r ∈ fixed, r ∉ clob) (hpc : ∀ p ∈ ptrs, p ≠ cnt)
    (hfc : cnt ∉ fixed)
    (hcon : ∀ g, IsG g → ∀ s, WP isa (.block (consts g)) s fun s' =>
      ((∀ r ∈ fixed, s'.gpr r = cv g r) ∧ s'.mem = s.mem ∧
        (∀ s'', s''.mem = s'.mem → Keep [cnt] s' s'' → J g 0 s'')) ∧ Keep kc s s')
    (hbody : GBody s₁ ptrs fixed outs clob cnt cv V J ins body) :
    WP isa (onGamma gr t fun g => .seq (.block (consts g)) (mapLoop ptrs cnt (body g))) s₁ fun s' =>
      ∃ sL, Keep (t :: kc) s₁ sL ∧ sL.mem = s₁.mem ∧
        Inv sL ptrs fixed outs (V (s₁.gpr gr).toNat) (J (s₁.gpr gr).toNat) 256 s' := by
  have hg' : (s₁.gpr gr).toNat = g32 ∨ (s₁.gpr gr).toNat = g88 := hg
  refine onGamma_ok htg hg' fun g hge s₂ k₂ hm₂ => ?_
  subst hge
  refine WP.seq (WP.mono (hcon _ hg s₂) fun sL ⟨⟨hcv, hmL, hJ⟩, kL⟩ => ?_)
  have k := k₂.trans kL
  have e : ∀ r ∈ ins ++ outs, sL.gpr r = s₁.gpr r := fun r hr => k.get r fun h => by
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    exacts [(hptr r hr).1 h, (hptr r hr).2 h]
  have hLL : Layout sL ins outs := hL.congr e k.rd k.wr
  refine WP.mono (loop_ok hLL hout hfix hpc hfc (fun s hm hk => hJ s hm hk)
    (hbody _ hg sL hLL hcv (by rw [hmL, hm₂]) e)) fun s' hI => ⟨sL, k.mono (by intro r hr; simpa using hr), by rw [hmL, hm₂], hI⟩

/-! ## The constants -/

/-- The constants of `Decompose`, `M` in `rm` and `2^(S-1)` in `ra`. -/
theorem hbConsts_ok (g : Nat) (hg : IsG g) (rm ra : Reg) (hr : rm ≠ ra) (s : State) :
    WP isa (.block (hbConsts g rm ra)) s fun s' =>
      (s'.gpr rm = BitVec.ofNat 64 (hbMul g) ∧ s'.gpr ra = BitVec.ofNat 64 (hbAdd g) ∧ s'.mem = s.mem) ∧
        Keep [rm, ra] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by simp [VG.Proof.MlDsa.AArch64.Arith.writesOnly,
    Code.allInstrs, hbConsts, dstOf])
  unfold hbConsts
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits, show 16 * 0 < 64 by decide,
    show 16 * 1 < 64 by decide, ite_true, RegUpd.gpr_write, RegUpd.mem_write, Option.some.injEq,
    exists_eq_left', hr, hr.symm, ite_false]
  rcases hg with rfl | rfl <;> exact ⟨by decide, by decide, trivial⟩

end VG.Proof.MlDsa.AArch64.Round
