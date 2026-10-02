import VerifiedGarbage.Proof.X448.AArch64.Fast.Iter
import VerifiedGarbage.Proof.X448.AArch64.Weak.FinalSwap

/-!
# X448 on AArch64: all 448 ladder iterations, and the final swap

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X1 X2 Z2 X3 Z3 A B C D AA BB E DA CB T0 T1 T2 T3 T4 T5 T6 T7 SWAP BITS ACC TMP)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot mask)
open VG.Proof.X448.AArch64.Weak (Index Env setCounter_ok opSwap swapMask_ok)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib)
open VG.Proof.X448 (bit)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem loop_ok {s₀ : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 448 → LInv base k u s₀ s n →
      WP isa (.loop Impl.X448.AArch64.Fast.step (.nonzero .x .x19)) s fun s' => LInv base k u s₀ s' 0 := by
  intro n s h1 h2 hi
  refine WP.loop (M := isa) (body := Impl.X448.AArch64.Fast.step) (c := .nonzero .x .x19)
    (Q := fun s' => LInv base k u s₀ s' 0)
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 448 ∧ LInv base k u s₀ s m) ?_ n s ⟨h1, h2, hi⟩
  intro m s ⟨h1, h2, hi⟩
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  refine WP.mono (step_ok (by omega) hbits hi) fun s' ⟨hi', hz⟩ => ?_
  simp only [eval, State.read, BitVec.setWidth_eq, bne, hz]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact .inl ⟨rfl, hi'⟩
  · refine .inr ⟨by simp only [decide_eq_false (by omega : ¬m = 0), Bool.not_false], m, by omega,
      by omega, by omega, hi'⟩

theorem ladder_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Spec.X448.Fe}
    (hbits : ∀ t < 448, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : ∀ s', s'.gpr .x19 = BitVec.ofNat 64 448 → (∀ r, r ≠ .x19 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → LInv base k u s₀ s' 448) :
    WP isa Impl.X448.AArch64.Fast.ladder s fun s' => LInv base k u s₀ s' 0 :=
  WP.seq (WP.mono (setCounter_ok s 448 (by decide))
    fun s' ⟨h1, h2, h3, h4, h5⟩ => loop_ok hbits 448 s' (by omega) (by omega) (hi s' h1 h2 h3 h4 h5))

theorem cswapE {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (x y : Index) (hxy : x ≠ y) {sw : Bool} (hm : s.gpr .x6 = mask sw) :
    WP isa (.block (Impl.Curve448.AArch64.cswap (slot x.val) (slot y.val))) s fun t =>
      FKeep base s t ∧ BEnv t.mem base ∧ t.gpr .x6 = s.gpr .x6 ∧
      (∀ j < 8, limbs t.mem base (slot x.val) j = if sw then limbs s.mem base (slot y.val) j
        else limbs s.mem base (slot x.val) j) ∧
      (∀ j < 8, limbs t.mem base (slot y.val) j = if sw then limbs s.mem base (slot x.val) j
        else limbs s.mem base (slot y.val) j) ∧
      Same base [x, y] s.mem t.mem ∧ EV t.mem base = opSwap x y sw (EV s.mem base) := by
  refine WP.mono (VG.Proof.Curve448.AArch64.cswap_ok hs (VG.Proof.X448.AArch64.Weak.slot_bound x)
    (VG.Proof.X448.AArch64.Weak.slot_bound y) (VG.Proof.X448.AArch64.Weak.slot_aligned x)
    (VG.Proof.X448.AArch64.Weak.slot_aligned y) (VG.Proof.X448.AArch64.Weak.slot_sep hxy) hm)
    fun t ⟨tx, ty, tm, tk⟩ => ?_
  have sm : Same base [x, y] s.mem t.mem := by
    intro i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    have ex := VG.Proof.X448.AArch64.Weak.slot_sep hi.1
    have ey := VG.Proof.X448.AArch64.Weak.slot_sep hi.2
    have hi' := VG.Proof.X448.AArch64.Weak.slot_bound i
    change (word t.mem base (slot i.val + 8 * j)).toNat = _
    rw [tm.word (by omega) (by omega) (by change slot i.val + 128 ≤ 3584 at hi'; omega)]
  have fx : EV t.mem base x = if sw then EV s.mem base y else EV s.mem base x := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Wide.valN_congr <;> exact tx
  have fy : EV t.mem base y = if sw then EV s.mem base x else EV s.mem base y := by
    cases sw <;> apply congrArg VG.Proof.X448.toFe <;> apply VG.Proof.X448.Wide.valN_congr <;> exact ty
  refine ⟨⟨tk.mono ?_, ?_⟩, fun i => ?_, tk.1 _ (by decide), tx, ty, sm, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide
  · intro p hp _
    have hx := x.isLt
    have hy := y.isLt
    apply tm p <;> simp only [slot] <;> omega
  · by_cases hix : i = x
    · subst i; intro j hj; rw [tx j hj]; cases sw <;> exact hb _ j hj
    · by_cases hiy : i = y
      · subst i; intro j hj; rw [ty j hj]; cases sw <;> exact hb _ j hj
      · exact sm.bnd (by simp [hix, hiy]) (hb i)
  · funext i
    by_cases hiy : i = y
    · subst i; rw [opSwap, Function.update_self]; exact fy
    · rw [opSwap, Function.update_of_ne hiy]
      by_cases hix : i = x
      · subst i; rw [Function.update_self]; exact fx
      · rw [Function.update_of_ne hix]
        exact sm.env (by simp [hix, hiy])

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block Impl.X448.AArch64.Weak.lastSwap) s fun t => FKeep base s t ∧ BEnv t.mem base ∧
      EV t.mem base = opSwap 2 4 (decide (sw = 1)) (opSwap 1 3 (decide (sw = 1)) (EV s.mem base)) := by
  rw [Impl.X448.AArch64.Weak.lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : FKeep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  have ts := kt.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (cswapE ts (tm ▸ hb) 1 3 (by decide) tc) fun u ⟨ku, bu, cu, _, _, _, eu⟩ => ?_
  refine WP.mono (cswapE (ku.scr ts) bu 2 4 (by decide) (cu.trans tc)) fun v ⟨kv, bv, _, _, _, _, ev⟩ =>
    ⟨kt.trans (ku.trans kv), bv, by rw [ev, eu, tm]⟩

end VG.Proof.X448.AArch64.Fast
