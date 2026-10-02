import VerifiedGarbage.Proof.X448.AArch64.Weak.Env
import VerifiedGarbage.Proof.Curve448.AArch64.Legacy
import VerifiedGarbage.Proof.X448.AArch64.Finish
namespace VG.Proof.X448.AArch64.Weak
open VG VG.AArch64
open VG.Impl.X448.AArch64 (slot ACC TMP SWAP)
open VG.Impl.X448.AArch64.Weak

/-- Convert each initialized field slot once, preserving the scalar and ABI saves. -/
theorem convert_ok {s : State} {base : Addr} (hs : Scr s base)
    (hb : VG.Proof.X448.AArch64.BoundedEnv s.mem base) :
    WP isa (.block convert) s fun t =>
      Keep base s t ∧ BoundedEnv t.mem base ∧ E t.mem base = VG.Proof.X448.AArch64.E s.mem base := by
  let inv := fun n (t : State) => Keep base s t ∧
    (∀ i : Index, i.val < n → Bounded t.mem base (slot i.val) ∧
      E t.mem base i = VG.Proof.X448.AArch64.E s.mem base i) ∧
    (∀ i : Index, n ≤ i.val → ∀ j < 16, limbs t.mem base (slot i.val) j = limbs s.mem base (slot i.val) j)
  have step : ∀ n t, n < 22 → inv n t →
      WP isa (.block (Impl.Curve448.AArch64.fromLegacy (slot n))) t (inv (n + 1)) := by
    intro n t hn ⟨tk, tv, tr⟩
    let o : Index := ⟨n, hn⟩
    have ov : o.val = n := rfl
    have bo : VG.Proof.X448.AArch64.Bounded t.mem base (slot n) := by
      intro j hj; rw [tr o (by omega) j hj]; exact hb o j hj
    refine WP.mono (VG.Proof.Curve448.AArch64.fromLegacy_ok (tk.scr hs)
      (slot_bound o) (slot_aligned o) bo) fun u ⟨uk, ub, uv⟩ => ?_
    refine ⟨tk.trans (VG.Proof.X448.AArch64.Op.keep (o := o) uk), ?_, ?_⟩
    · intro i hi
      by_cases he : i = o
      · subst i
        refine ⟨ub, ?_⟩
        change F u.mem base (slot n) = _
        have uv' : F u.mem base (slot n) = VG.Proof.X448.AArch64.F t.mem base (slot n) := uv
        rw [uv']
        exact congrArg toFe (VG.Proof.X448.valN_congr (tr o (by omega)))
      · have sep := slot_sep he
        have before : i.val < n := by have := i.isLt; have hne : i.val ≠ n := fun e => he (Fin.ext e); omega
        have old := tv i before
        refine ⟨?_, ?_⟩
        · intro j hj
          rw [uk.mem.limbs sep (slot_bound i) (by omega : j < 16)]; exact old.1 j hj
        · exact (congrArg toFe (VG.Proof.Curve448.AArch64.field_fe uk.mem sep (slot_bound i))).trans old.2
    · intro i hi j hj
      have he : i ≠ o := by intro e; subst i; change n + 1 ≤ n at hi; omega
      rw [uk.mem.limbs (slot_sep he) (slot_bound i) hj]
      exact tr i (by omega) j hj
  refine WP.mono (wp_range_flatMap (M := isa) (N := 22) inv step 22 (by decide) s
    ⟨Keep.refl _ _, fun i hi => by omega, fun _ _ _ _ => rfl⟩) fun t ⟨tk, tv, _⟩ => ?_
  exact ⟨tk, fun i => (tv i i.isLt).1, funext fun i => (tv i i.isLt).2⟩

def setupRegs : List Reg := .x20 :: .x12 :: workRegs

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ t.gpr .x20 = s.gpr .x0 ∧ Keeps setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧
      E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E t.mem base 1 = 1 ∧ E t.mem base 2 = 0 ∧
      E t.mem base 3 = E t.mem base 0 ∧ E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  rw [setup, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.setup_ok hc hw hn hp hr hd)
    fun u ⟨us, ub, up, uk, um, uv, u0, u1, u2, u3, u4, uw⟩ => ?_
  refine WP.mono (convert_ok us ub) fun t ⟨tk, tb, te⟩ => ?_
  refine ⟨tk.scr us, tb, (tk.regs.1 _ (by decide)).trans up,
    (uk.mono (by decide)).trans (tk.regs.mono (by decide)),
    um.trans (tk.mem.whole (by decide) (by decide)),
    uv.outside2 tk.mem (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [te]; exact u0
  · rw [te]; exact u1
  · rw [te]; exact u2
  · rw [te]; exact u3
  · rw [te]; exact u4
  · rw [tk.mem.word (d := SWAP) (by decide) (by decide) (by decide)]; exact uw
end VG.Proof.X448.AArch64.Weak
