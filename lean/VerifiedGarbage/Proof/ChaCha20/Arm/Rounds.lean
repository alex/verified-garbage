import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.ChaCha20.Spec
import VerifiedGarbage.Impl.ChaCha20.Arm
import Mathlib.Tactic.IntervalCases

/-!
# ChaCha20 block function on 32-bit ARM: the rounds

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.ChaCha20.Arm

open VG VG.Arm VG.Impl.ChaCha20.Arm VG.Proof.ChaCha20
open VG.Spec.ChaCha20 (Word quarterRound qround innerBlock)

theorem qr_ok {a b c d : Reg} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (s : State) (va vb vc vd : Word)
    (ha : s.gpr a = va) (hb : s.gpr b = vb) (hc : s.gpr c = vc) (hd : s.gpr d = vd) :
    WP isa (.block (qr a b c d)) s fun s' =>
      s'.gpr a = (quarterRound va vb vc vd).1 ∧ s'.gpr b = (quarterRound va vb vc vd).2.1 ∧
      s'.gpr c = (quarterRound va vb vc vd).2.2.1 ∧ s'.gpr d = (quarterRound va vb vc vd).2.2.2 ∧
      (∀ r, r ≠ a → r ≠ b → r ≠ c → r ≠ d → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [qr, runBlock_cons, runStep_some,
    runBlock_nil, exec, Op2.eval, isa, State.setReg, ha, hb,
    hc, hd, hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm, hbc.symm, hbd.symm,
    hcd.symm, ite_true, ite_false, Option.map_some, Option.some.injEq,
    exists_eq_left']
  and_intros
  all_goals first
    | simp only [quarterRound_eq]
    | (intro r h1 h2 h3 h4; simp [h1, h2, h3, h4])

/-! ## Where the words are -/

/-- Word `k` is in its register `wreg k` (rather than its slot) when the
third-row word in `lr` is `c`: always, except for the third-row words other
than `c`. -/
def inReg (c k : Nat) : Bool := !(8 ≤ k && k ≤ 11) || k == c

/-- The home slot of word `k` (8–11), relative to the 64-bit address `B` of `buf`. -/
abbrev slotAddr (B : Addr) (k : Nat) : Addr := B + BitVec.ofNat 64 (slotOff k)

/-- The state `v` is in the registers and slots, with word `c` in `lr`. -/
def Holds (B : Addr) (c : Nat) (v : CState) (s : State) : Prop :=
  ∀ k (hk : k < 16), if inReg c k then s.gpr (wreg k) = v[k] else s.mem.readW (slotAddr B k) 32 = v[k]

theorem wreg_ne_r1 (k : Nat) : wreg k ≠ .r1 := by
  unfold wreg; split <;> decide

/-! ## One quarter round -/

/-- The side conditions of `quarter_ok`, decidable for concrete arguments. -/
def QSide (c x y z w : Nat) : Bool :=
  inReg c x && inReg c y && inReg c z && inReg c w && [x, y, z, w].Nodup &&
  [wreg x, wreg y, wreg z, wreg w].Nodup &&
  (List.range 16).all fun k => [x, y, z, w].contains k || !inReg c k ||
    !([wreg x, wreg y, wreg z, wreg w].contains (wreg k))

theorem quarter_ok {c x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : QSide c x y z w = true) {B : Addr} {v : CState} {s : State} (h : Holds B c v s) :
    WP isa (quarter x y z w) s fun s' =>
      Holds B c (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s' ∧ s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .r1 = s.gpr .r1 := by
  simp only [QSide, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hq
  obtain ⟨⟨⟨⟨⟨⟨ix, iy⟩, iz⟩, iw⟩, nd⟩, nr⟩, others⟩ := hq
  have nd' : (x ≠ y ∧ x ≠ z ∧ x ≠ w) ∧ (y ≠ z ∧ y ≠ w) ∧ z ≠ w := by simpa using nd
  have nr' : (wreg x ≠ wreg y ∧ wreg x ≠ wreg z ∧ wreg x ≠ wreg w) ∧
      (wreg y ≠ wreg z ∧ wreg y ≠ wreg w) ∧ wreg z ≠ wreg w := by simpa using nr
  obtain ⟨⟨nxy, nxz, nxw⟩, ⟨nyz, nyw⟩, nzw⟩ := nd'
  obtain ⟨⟨rxy, rxz, rxw⟩, ⟨ryz, ryw⟩, rzw⟩ := nr'
  have gx := h x hx; have gy := h y hy; have gz := h z hz; have gw := h w hw
  simp only [ix, iy, iz, iw, ite_true] at gx gy gz gw
  refine WP.mono (qr_ok rxy rxz rxw ryz ryw rzw s _ _ _ _ gx gy gz gw)
    fun _ ⟨ha, hb, hc, hd, hr, hm, hrd, hwr⟩ => ⟨fun k hk => ?_, hm, hrd, hwr,
      hr _ (wreg_ne_r1 x).symm (wreg_ne_r1 y).symm (wreg_ne_r1 z).symm (wreg_ne_r1 w).symm⟩
  rw [qround_get _ _ _ _ _ k hk]
  simp only
  by_cases ew : w = k
  · subst ew; simp only [iw, ite_true]; exact hd
  by_cases ez : z = k
  · subst ez; simp only [iz, ite_true, ew]; exact hc
  by_cases ey : y = k
  · subst ey; simp only [iy, ite_true, ew, ez]; exact hb
  by_cases ex : x = k
  · subst ex; simp only [ix, ite_true, ew, ez, ey]; exact ha
  simp only [ew, ez, ey, ex, ite_false]
  have hk' := h k hk
  have ho := others k hk
  split
  · rename_i hin
    simp only [hin, ite_true] at hk'
    have ho' : wreg k ≠ wreg x ∧ wreg k ≠ wreg y ∧ wreg k ≠ wreg z ∧ wreg k ≠ wreg w := by
      simpa [Ne.symm ex, Ne.symm ey, Ne.symm ez, Ne.symm ew, hin] using ho
    rw [hr _ ho'.1 ho'.2.1 ho'.2.2.1 ho'.2.2.2]; exact hk'
  · rename_i hin
    simp only [hin] at hk'
    rw [hm]; exact hk'

/-! ## Swapping the third-row word in `lr` -/

/-- The four home slots. -/
abbrev slotR (B : Addr) : Region := ⟨B + BitVec.ofNat 64 128, 16⟩

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h

theorem slot_in_slotR (B : Addr) {k : Nat} (h8 : 8 ≤ k) (h11 : k ≤ 11) :
    (slotR B).Contains (slotAddr B k) 4 := by
  simp only [Region.Contains, slotAddr, slotOff]
  rw [show B + BitVec.ofNat 64 (128 + 4 * (k - 8)) - (B + BitVec.ofNat 64 128) =
    BitVec.ofNat 64 (4 * (k - 8)) by bv_omega, toNat_ofNat_lt (by omega)]
  omega

theorem slot_sep (B : Addr) {j k : Nat} (hj8 : 8 ≤ j) (hj : j ≤ 11) (hk8 : 8 ≤ k) (hk : k ≤ 11)
    (h : j ≠ k) : Mem.Sep (slotAddr B j) 4 (slotAddr B k) 4 := by
  intro x hx hy
  simp only [slotAddr, slotOff] at hx hy
  bv_omega

/-- The rounds invariant, relative to the state `s₀` at the start of the rounds. -/
structure RI (B : Addr) (c : Nat) (v : CState) (s₀ s : State) : Prop where
  holds : Holds B c v s
  frame : Frame [slotR B] s₀.mem s.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  r1 : s.gpr .r1 = s₀.gpr .r1

theorem quarter_step {c x y z w : Nat} (hx : x < 16) (hy : y < 16) (hz : z < 16) (hw : w < 16)
    (hq : QSide c x y z w = true) {B : Addr} {v : CState} {s₀ s : State} (h : RI B c v s₀ s) :
    WP isa (quarter x y z w) s (RI B c (qround v ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ ⟨w, hw⟩) s₀) :=
  WP.mono (quarter_ok hx hy hz hw hq h.holds) fun _ ⟨hh, hm, hrd, hwr, hr1⟩ =>
    ⟨hh, hm ▸ h.frame, hrd.trans h.rd, hwr.trans h.wr, hr1.trans h.r1⟩

theorem swap_step {i j : Nat} (hi8 : 8 ≤ i) (hi : i ≤ 11) (hj8 : 8 ≤ j) (hj : j ≤ 11) (hij : i ≠ j)
    {B : Addr} {v : CState} {s₀ s : State} (h : RI B i v s₀ s)
    (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
    (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr) :
    WP isa (swap i j) s (RI B j v s₀) := by
  have ea : ∀ off, off < 256 → State.addr (s.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off :=
    fun off ho => by rw [h.r1]; exact haddr off ho
  have cb : ∀ k, 8 ≤ k → k ≤ 11 → (⟨B, 256⟩ : Region).Contains (slotAddr B k) 4 := fun k h1 h2 => by
    simp only [Region.Contains, slotAddr, slotOff]
    rw [show B + BitVec.ofNat 64 (128 + 4 * (k - 8)) - B = BitVec.ofNat 64 (128 + 4 * (k - 8)) by
      bv_omega, toNat_ofNat_lt (by omega)]
    omega
  have hout : InRegions s.wr (slotAddr B i) 4 := ⟨_, h.wr ▸ hw, cb i hi8 hi⟩
  have hin : InRegions (s.rd ++ s.wr) (slotAddr B j) 4 :=
    ⟨_, List.mem_append_right _ (h.wr ▸ hw), cb j hj8 hj⟩
  have hi' : inReg i i = true := by simp [inReg]
  have hl := h.holds i (by omega)
  simp only [hi', ite_true] at hl
  have hj' : inReg i j = false := by simp [inReg, hij.symm]; omega
  have hv := h.holds j (by omega)
  simp only [hj'] at hv
  have wi : wreg i = .lr := by interval_cases i <;> rfl
  have wj : wreg j = .lr := by interval_cases j <;> rfl
  rw [wi] at hl
  apply WP.of_runBlock
  simp only [runBlock_cons, isa]
  rw [exec_str (by simp only [slotOff]; omega) (by rw [ea _ (by simp only [slotOff]; omega)]; exact hout)]
  simp only [runStep_some, runBlock_cons]
  rw [exec_ldr (by simp only [slotOff]; omega)
    (by show InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r1 + BitVec.ofNat 32 (slotOff j))) 4
        rw [ea _ (by simp only [slotOff]; omega)]; exact hin)]
  simp only [runStep_some, runBlock_nil, Option.some.injEq, exists_eq_left', ea _ (show slotOff i < 256 by
    simp only [slotOff]; omega), ea _ (show slotOff j < 256 by simp only [slotOff]; omega)]
  rw [Mem.readW_writeW_sep (slot_sep B hj8 hj hi8 hi (Ne.symm hij)) (by decide)]
  refine ⟨fun k hk => ?_, ?_, h.rd, h.wr, ?_⟩
  · have hk' := h.holds k hk
    by_cases hkj : k = j
    · subst hkj
      simp only [inReg, beq_self_eq_true, Bool.or_true, ite_true, State.setReg, wj]
      simpa [slotAddr] using hv
    by_cases hki : k = i
    · subst hki
      have : inReg j k = false := by simp [inReg, hij]; omega
      simp only [this, Bool.false_eq_true, ite_false, State.setReg, slotAddr,
        Mem.readW_writeW_self32]
      exact hl
    · by_cases h811 : 8 ≤ k ∧ k ≤ 11
      · have e1 : inReg j k = false := by simp [inReg, hkj]; omega
        have e2 : inReg i k = false := by simp [inReg, hki]; omega
        simp only [e1, e2, Bool.false_eq_true, ite_false, State.setReg] at hk' ⊢
        rw [Mem.readW_writeW_sep (slot_sep B h811.1 h811.2 hi8 hi hki) (by decide)]; exact hk'
      · have e1 : inReg j k = true := by simp [inReg]; omega
        have e2 : inReg i k = true := by simp [inReg]; omega
        have ne : wreg k ≠ .lr := by
          intro e; apply h811
          interval_cases k <;> simp_all [wreg]
        simp only [e1, e2, ite_true, State.setReg, ne, ite_false] at hk' ⊢; exact hk'
  · exact h.frame.writeW (List.mem_singleton_self _) _ (slot_in_slotR B hi8 hi)
  · simp only [State.setReg, show Reg.r1 ≠ Reg.lr by decide, ite_false]; exact h.r1

/-! ## Double rounds -/

theorem doubleRound_ok {B : Addr} {v : CState} {s₀ s : State} (h : RI B 8 v s₀ s)
    (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
    (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr) :
    WP isa doubleRound s (RI B 8 (innerBlock v) s₀) := by
  unfold doubleRound
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 4) (z := 8) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h) fun _ h1 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 8) (j := 9) (by omega) (by omega) (by omega) (by omega)
    (by omega) h1 haddr hw) fun _ h2 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 5) (z := 9) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h2) fun _ h3 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 9) (j := 10) (by omega) (by omega) (by omega) (by omega)
    (by omega) h3 haddr hw) fun _ h4 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 6) (z := 10) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h4) fun _ h5 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 10) (j := 11) (by omega) (by omega) (by omega) (by omega)
    (by omega) h5 haddr hw) fun _ h6 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 7) (z := 11) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h6) fun _ h7 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 11) (j := 10) (by omega) (by omega) (by omega) (by omega)
    (by omega) h7 haddr hw) fun _ h8 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 0) (y := 5) (z := 10) (w := 15) (by decide) (by decide)
    (by decide) (by decide) (by decide) h8) fun _ h9 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 10) (j := 11) (by omega) (by omega) (by omega) (by omega)
    (by omega) h9 haddr hw) fun _ h10 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 1) (y := 6) (z := 11) (w := 12) (by decide) (by decide)
    (by decide) (by decide) (by decide) h10) fun _ h11 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 11) (j := 8) (by omega) (by omega) (by omega) (by omega)
    (by omega) h11 haddr hw) fun _ h12 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 2) (y := 7) (z := 8) (w := 13) (by decide) (by decide)
    (by decide) (by decide) (by decide) h12) fun _ h13 => ?_)
  refine WP.seq (WP.mono (swap_step (i := 8) (j := 9) (by omega) (by omega) (by omega) (by omega)
    (by omega) h13 haddr hw) fun _ h14 => ?_)
  refine WP.seq (WP.mono (quarter_step (x := 3) (y := 4) (z := 9) (w := 14) (by decide) (by decide)
    (by decide) (by decide) (by decide) h14) fun _ h15 => ?_)
  exact swap_step (i := 9) (j := 8) (by omega) (by omega) (by omega) (by omega) (by omega) h15 haddr hw

theorem rounds_ok {B : Addr} {v : CState} {s₀ : State} (h : Holds B 8 v s₀)
    (haddr : ∀ off, off < 256 → State.addr (s₀.gpr .r1 + BitVec.ofNat 32 off) = B + BitVec.ofNat 64 off)
    (hw : (⟨B, 256⟩ : Region) ∈ s₀.wr) :
    ∀ n, WP isa (rounds n) s₀ (RI B 8 (Nat.repeat innerBlock n v) s₀)
  | 0 => WP.block_nil ⟨h, Frame.refl _ _, rfl, rfl, rfl⟩
  | n + 1 => WP.seq (WP.mono (rounds_ok h haddr hw n) fun _ h' => doubleRound_ok h' haddr hw)

end VG.Proof.ChaCha20.Arm
