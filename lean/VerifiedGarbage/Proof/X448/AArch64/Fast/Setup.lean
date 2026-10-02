import VerifiedGarbage.Proof.X448.AArch64.Fast.Inv
import VerifiedGarbage.Proof.X448.AArch64.Weak.Setup

/-!
# X448 on AArch64: setup, saving `x21`–`x28`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot SWAP BITS ACC)
open VG.Impl.X448.AArch64.Fast (SAVE saved save restore)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot Saved)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib stw_ok)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

/-- `x21`–`x28` saved in the working space. -/
def SavedX (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ k < 8, word m base (SAVE + 8 * k) = g (saved k)

theorem SavedX.outside2 {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : SavedX base g m)
    {x nx y ny : Nat} (ho : Outside2 base x nx y ny m m') (hx : x + nx ≤ SAVE) (hy : SAVE + 64 ≤ y) :
    SavedX base g m' := fun k hk =>
  (ho.word (Or.inr (by omega)) (Or.inl (by omega)) (by simp only [SAVE]; omega)).trans (h k hk)

theorem SavedX.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : SavedX base g m)
    {o n : Nat} (ho : Outside base o n m m') (hx : o + n ≤ SAVE ∨ SAVE + 64 ≤ o) :
    SavedX base g m' := fun k hk =>
  (ho.word (by omega) (by simp only [SAVE]; omega)).trans (h k hk)

theorem saved_ne : ∀ k < 8, saved k ≠ .x3 ∧ saved k ≠ .x12 := by decide

theorem save_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block save) s fun t =>
      SavedX base s.gpr t.mem ∧ Outside base SAVE 64 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧
      t.wr = s.wr := by
  have e : save = (List.range 8).flatMap fun k => [st (saved k) (SAVE + 8 * k)] := by
    simp only [save]; rfl
  rw [e]
  let inv := fun n (t : State) =>
    (∀ k < n, word t.mem base (SAVE + 8 * k) = s.gpr (saved k)) ∧
    Outside base SAVE 64 s.mem t.mem ∧ t.gpr = s.gpr ∧ t.rd = s.rd ∧ t.wr = s.wr
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tO, tg, tr, tw⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), Outside.refl _ _ _ _, rfl, rfl, rfl⟩
  have ts : Scr t base := ⟨by rw [tg]; exact hs.x3, by rw [tg]; exact hs.mask, tw ▸ hs.wr, hs.nowrap⟩
  refine WP.mono (stw_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) fun u ⟨uw, uO, ug, ur, uwr⟩ => ⟨fun k hk => ?_,
      tO.trans (uO.mono (by omega) (by omega)), ug.trans tg, ur.trans tr, uwr.trans tw⟩
  rw [uw _ (by simp only [SAVE]; omega) (by omega)]
  by_cases h : k = n
  · subst h; rw [ite_eq_left rfl, tg]
  · rw [ite_eq_right (by omega)]; exact tv k (by omega)

theorem saved_not_setup : ∀ k < 8, saved k ∉ VG.Proof.X448.AArch64.Weak.setupRegs := by decide

theorem weak_bnd {m : Mem} {base : Addr} {o : Nat} (h : VG.Proof.Curve448.AArch64.Bounded m base o) :
    Bnd Mb m base o := fun i hi => Nat.lt_of_lt_of_le (h i hi) (by decide)

theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .x3 = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .x2 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block Impl.X448.AArch64.Fast.setup) s fun t =>
      Scr t base ∧ BEnv t.mem base ∧ (∀ i : Index, Bnd Mb t.mem base (slot i.val)) ∧
      t.gpr .x20 = s.gpr .x0 ∧ Keeps VG.Proof.X448.AArch64.Weak.setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧ SavedX base s.gpr t.mem ∧
      EV t.mem base 0 = VG.Proof.X448.toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      EV t.mem base 1 = 1 ∧ EV t.mem base 2 = 0 ∧
      EV t.mem base 3 = EV t.mem base 0 ∧ EV t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  rw [Impl.X448.AArch64.Fast.setup, WP.block_append_iff]
  refine WP.mono (VG.Proof.X448.AArch64.Weak.setup_ok hc hw hn hp hr hd)
    fun u ⟨us, ub, ux, uk, um, uv, u0, u1, u2, u3, u4, uw⟩ => ?_
  refine WP.mono (save_ok us) fun t ⟨tv, tO, tg, tr, tw⟩ => ?_
  have sl : ∀ i : Index, ∀ j < 8, limbs t.mem base (slot i.val) j = limbs u.mem base (slot i.val) j := by
    intro i j hj
    have hi := i.isLt
    have hS : SAVE = 3520 := rfl
    exact tO.limbs (Or.inl (by simp only [slot]; omega)) (by simp only [slot]; omega) (by omega)
  have sm : Same base [] u.mem t.mem := fun i _ j hj => sl i j hj
  have red : ∀ i : Index, Bnd Mb t.mem base (slot i.val) := fun i => sm.bnd (by simp) (weak_bnd (ub i))
  have ug : ∀ r, t.gpr r = u.gpr r := fun r => by rw [tg]
  refine ⟨⟨(ug _).trans us.x3, (ug _).trans us.mask, tw ▸ us.wr, us.nowrap⟩,
    fun i j hj => Nat.lt_of_lt_of_le (red i j hj) VG.Proof.Curve448.AArch64.Fast.Mb_le_Ib, red, (ug _).trans ux,
    ⟨fun r hr => (ug r).trans (uk.1 r hr), tr.trans uk.2.1, tw.trans uk.2.2⟩,
    um.trans ?_, uv.outside tO (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx; exact tO x (by simp only [SAVE]; omega)
  · intro k hk; rw [tv k hk, uk.1 _ (saved_not_setup k hk)]
  · rw [sm.env (by simp)]; exact u0
  · rw [sm.env (by simp)]; exact u1
  · rw [sm.env (by simp)]; exact u2
  · rw [sm.env (by simp), sm.env (by simp)]; exact u3
  · rw [sm.env (by simp)]; exact u4
  · rw [tO.word (Or.inl (by decide)) (by decide)]; exact uw

end VG.Proof.X448.AArch64.Fast
