import VerifiedGarbage.Proof.X448.AArch64.Fast.Setup
import VerifiedGarbage.Proof.X448.AArch64.Weak.Finish

/-!
# X448 on AArch64: the result, and restoring the callee-saved registers

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.X448.AArch64.Fast

open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st slot X2 T7 SWAP BITS ACC)
open VG.Impl.X448.AArch64.Fast (SAVE VSAVE saved save restore)
open VG.Proof.X448.AArch64 (Keeps Scr word off Outside Outside2 limbs FieldMem ofs Slot Saved Op freeze_ok
  output_ok output_word restore_ok)
open VG.Proof.X448.AArch64.Weak (Index Env)
open VG.Proof.Curve448.AArch64.Fast (Mb Ib ld_ok)

local notation "EV" => VG.Proof.X448.AArch64.Weak.E

theorem restoreX_ok {s : State} {base : Addr} (hs : Scr s base) {g : Reg → BitVec 64}
    (hsv : SavedX base g s.mem) :
    WP isa (.block restore) s fun t =>
      (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧ t.mem = s.mem ∧
      Keeps [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t := by
  have e : restore = (List.range 8).flatMap fun k => [ld (saved k) (SAVE + 8 * k)] := by
    simp only [restore]; rfl
  rw [e]
  have sinj : ∀ k < 8, ∀ j < 8, j ≠ k → saved j ≠ saved k := by decide
  have smem : ∀ k < 8, saved k ∈ [Reg.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] := by decide
  let inv := fun n (t : State) =>
    (∀ k < n, t.gpr (saved k) = g (saved k)) ∧ t.mem = s.mem ∧
      Keeps [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28] s t
  refine wp_range_flatMap (M := isa) (N := 8) inv (fun n t hn ⟨tv, tm, tk⟩ => ?_) 8 (by decide) s
    ⟨fun _ h => absurd h (Nat.not_lt_zero _), rfl, Keeps.refl _ _⟩
  have ts : Scr t base := hs.of_keeps tk (by decide)
  refine WP.mono (ld_ok ts (saved n) (d := SAVE + 8 * n) (by simp only [SAVE]; omega)
    (by simp only [SAVE]; omega)) fun u ⟨uv, um, uk⟩ => ⟨fun k hk => ?_, um.trans tm, tk.trans (uk.mono ?_)⟩
  · by_cases h : k = n
    · subst h; rw [uv, tm]; exact hsv k hn
    · rw [uk.1 _ (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact sinj n hn k (by omega) h)]
      exact tv k (by omega)
  · intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rw [hr]; exact smem n hn

def finishRegs : List Reg := .x19 :: .x20 :: fclob

theorem finish_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : BEnv s.mem base)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) {g : Reg → BitVec 64} (sv : Saved base g s.mem)
    (svx : SavedX base g s.mem) {gv : VReg → BitVec 128} (svV : SavedV base gv s.mem) :
    WP isa Impl.X448.AArch64.Fast.finish s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ (∀ k < 8, t.gpr (saved k) = g (saved k)) ∧
      (∀ k < 8, (t.v (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64 =
        (gv (VG.Impl.Curve448.AArch64.Neon.V (8 + k))).extractLsb' 0 64) ∧
      Keeps finishRegs s t ∧ Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (EV s.mem base 1 * EV s.mem base 21) := by
  rw [Impl.X448.AArch64.Fast.finish]
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fmulE hs hb 1 1 21 (by decide)) fun u ⟨uk, ub, um, us, ue⟩ => ?_
  have us₀ := uk.scr hs
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok' us₀ (o := X2) (by decide) (by decide)
    (fun i hi => Nat.lt_trans (um i hi) (by decide))) fun u' ⟨ck, cb, cv⟩ => ?_
  have uv : VG.Proof.X448.AArch64.F u'.mem base X2 = EV s.mem base 1 * EV s.mem base 21 := by
    rw [cv]
    change EV u.mem base 1 = _
    rw [ue]; simp only [VG.Proof.X448.AArch64.opMul, Function.update_self]
  have us := us₀.of_keeps ck.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok us cb) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs vb ((vk.1 _ (by decide)).trans ((ck.1.1 _ (by decide)).trans
    ((uk.regs.1 _ (by decide)).trans hp)))
    (by intro j hj; rw [vk.2.2, ck.1.2.2, uk.regs.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := ((sv.outside2 uk.mem (by decide) (by decide)).field ck.2 (by decide)).field vm (by decide)
  have svw : Saved base g w.mem :=
    ⟨(output_word wm (by decide) (by decide) hfar).trans svv.1,
      (output_word wm (by decide) (by decide) hfar).trans svv.2⟩
  have sxv : SavedX base g v.mem := by
    intro k hk
    have hS : SAVE = 3520 := rfl
    rw [vm.word (Or.inr (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)) (by simp only [ACC]; omega),
      ck.2.word (Or.inr (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)) (by simp only [ACC]; omega),
      uk.mem.word (Or.inr (by omega)) (Or.inl (by simp only [ACC]; omega)) (by omega)]
    exact svx k hk
  have sxw : SavedX base g w.mem := fun k hk =>
    (output_word wm (by decide) (by simp only [SAVE]; omega) hfar).trans (sxv k hk)
  rw [WP.block_append_iff]
  refine WP.mono (restore_ok ws svw) fun t ⟨tb, tr, tm, tk⟩ => ?_
  have tsx : SavedX base g t.mem := by rw [tm]; exact sxw
  have ts := ws.of_keeps tk (by decide)
  have hV : VSAVE = 4736 := rfl
  have vsw : SavedV base gv w.mem :=
    ((((svV.outside2 uk.mem (by decide) (by decide)).field ck.2 (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)).field
      vm (by simp only [X2, VG.Impl.X448.AArch64.slot]; omega)).output wm (by decide) hfar)
  rw [WP.block_append_iff]
  refine WP.mono (restoreX_ok ts tsx) fun z ⟨zv, zm, zk⟩ => ?_
  have zs := ts.of_keeps zk (by decide)
  refine WP.mono (vrestore_ok zs (v := gv) (by rw [zm, tm]; exact vsw)) fun z' ⟨zvv, zm', zg', zr', zw'⟩ => ?_
  have zk' : Keeps [] z z' := ⟨fun r _ => congrFun zg' r, zr', zw'⟩
  refine ⟨(zg' ▸ zk.1 _ (by decide)).trans tb, (zg' ▸ zk.1 _ (by decide)).trans tr, fun k hk => zg' ▸ zv k hk, zvv,
    (uk.regs.mono ?_).trans ((ck.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans
      ((tk.mono ?_).trans ((zk.mono ?_).trans (zk'.mono ?_)))))), ?_, ?_⟩
  all_goals try (intro r hr; revert r; decide)
  · rw [zm', zm, tm]
    exact ((((uk.mem.whole (by decide) (by decide)).trans ((ck.2.whole (by decide)).trans
      (vm.whole (by decide)))).frame.mono (by simp)).trans (wm.frame.mono (by simp)))
  · rw [zm', zm, tm, wv, vv, VG.Proof.X448.encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.AArch64.Fast
