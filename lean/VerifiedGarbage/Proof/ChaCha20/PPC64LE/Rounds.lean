import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Exec
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.PPC64LE

/-!
# ChaCha20 block function on PPC64LE: the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.PPC64LE

open VG VG.PPC64LE VG.Impl.ChaCha20.PPC64LE VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (s : State) (va vb vc vd : Word)
    (ha : (s.gpr a).setWidth 32 = va) (hb : (s.gpr b).setWidth 32 = vb)
    (hc : (s.gpr c).setWidth 32 = vc) (hd : (s.gpr d).setWidth 32 = vd) :
    WP isa (.block (qr a b c d)) s fun s' =>
      (s'.gpr a).setWidth 32 = (quarterRound va vb vc vd).1 ∧
      (s'.gpr b).setWidth 32 = (quarterRound va vb vc vd).2.1 ∧
      (s'.gpr c).setWidth 32 = (quarterRound va vb vc vd).2.2.1 ∧
      (s'.gpr d).setWidth 32 = (quarterRound va vb vc vd).2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [qr, runBlock_cons, runStep_some,
    runBlock_nil, exec_add, exec_logic,
    exec_rotr_w (show 16 < 32 by decide), exec_rotr_w (show 20 < 32 by decide),
    exec_rotr_w (show 24 < 32 by decide), exec_rotr_w (show 25 < 32 by decide), isa,
    State.write, hab, hac, had, hbc, hbd, hcd, hab.symm,
    hac.symm, had.symm, hbc.symm, hbd.symm, hcd.symm, ite_true, ite_false, Option.some.injEq,
    exists_eq_left']
  simp (config := {decide := true}) only [lo32_add, BitVec.setWidth_xor,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, ha, hb, hc, hd]
  and_intros
  all_goals first
    | simp only [quarterRound_eq]
    | (intro r h1 h2 h3 h4; simp [h1, h2, h3, h4])

/-! ## Where the words are -/

/-- The state `v` is in the registers. -/
def Holds (v : CState) (s : State) : Prop := ∀ k (hk : k < 16), (s.gpr (wreg k)).setWidth 32 = v[k]

/-- The registers that hold state words. -/
def Words (r : Reg) : Prop := ∃ k < 16, r = wreg k

theorem wreg_inj {j k : Nat} (hj : j < 16) (hk : k < 16) (h : wreg j = wreg k) : j = k := by
  have key : ∀ j, j < 16 → ∀ k, k < 16 → wreg j = wreg k → j = k := by decide
  exact key j hj k hk h

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (v : CState) (s₀ s : State) : Prop where
  holds : Holds v s
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, ¬ Words r → s.gpr r = s₀.gpr r

theorem quarter_step {x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hd : [x, y, z, w].Nodup) {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa (quarter x y z w) s (RI (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) := by
  have nd : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using hd
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd
  have ne : ∀ {i j}, i < 16 → j < 16 → i ≠ j → wreg i ≠ wreg j := fun hi hj hij e =>
    hij (wreg_inj hi hj e)
  refine WP.mono (qr_ok (ne hx hy nxy) (ne hx hz nxz) (ne hx hw nxw) (ne hy hz nyz)
    (ne hy hw nyw) (ne hz hw nzw) s _ _ _ _ (h.holds x hx) (h.holds y hy) (h.holds z hz)
    (h.holds w hw)) fun s' ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ =>
    ⟨fun k hk => ?_, hm.trans h.mem, hrd.trans h.rd, hwr.trans h.wr, fun r hr' => ?_⟩
  · rw [qround_get _ _ _ _ _ k hk]
    simp only
    by_cases ew : w = k
    · subst ew; simp only [ite_true]; exact hd
    by_cases ez : z = k
    · subst ez; simp only [ite_true, ew, ite_false]; exact hc
    by_cases ey : y = k
    · subst ey; simp only [ite_true, ew, ez, ite_false]; exact hb
    by_cases ex : x = k
    · subst ex; simp only [ite_true, ew, ez, ey, ite_false]; exact ha
    simp only [ew, ez, ey, ex, ite_false]
    rw [hr _ (ne hk hx (Ne.symm ex)) (ne hk hy (Ne.symm ey)) (ne hk hz (Ne.symm ez))
      (ne hk hw (Ne.symm ew))]
    exact h.holds k hk
  · have nw : ∀ i < 16, r ≠ wreg i := fun i hi e => hr' ⟨i, hi, e⟩
    rw [hr r (nw x hx) (nw y hy) (nw z hz) (nw w hw)]
    exact h.keep r hr'

theorem doubleRound_ok {v : CState} {s₀ s : State} (h : RI v s₀ s) :
    WP isa doubleRound s (RI (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₂) fun s₃ h₃ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₃) fun s₄ h₄ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₄) fun s₅ h₅ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₅) fun s₆ h₆ => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₆) fun s₇ h₇ => ?_)
  exact WP.mono (quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h₇) fun _ h => h

theorem rounds_ok {v : CState} {s₀ : State} (h : Holds v s₀) :
    ∀ n, WP isa (rounds n) s₀ (RI (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, rfl, rfl, rfl, fun _ _ => rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h n) fun _ h' => doubleRound_ok h')

end VG.Proof.ChaCha20.PPC64LE
