import VerifiedGarbage.Proof.X448.AArch64.Weak.Setup
import VerifiedGarbage.Proof.X448.AArch64.Finish
namespace VG.Proof.X448.AArch64.Weak
open VG VG.AArch64
open VG.Impl.X448.AArch64 (ld st X2 T7 ACC)
open VG.Impl.X448.AArch64.Weak
def finishRegs : List Reg := .x19 :: .x20 :: workRegs

theorem finish_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hp : s.gpr .x1 = p) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) {g : Reg → BitVec 64} (sv : Saved base g s.mem) :
    WP isa finish s fun t =>
      t.gpr .x19 = g .x19 ∧ t.gpr .x20 = g .x20 ∧ Keeps finishRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (E s.mem base 1 * E s.mem base 21) := by
  refine WP.seq (WP.mono (VG.Proof.Curve448.AArch64.mul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us₀ := hs.of_keeps uk.1 (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Curve448.AArch64.toLegacy_ok us₀ (o := X2)
    (by decide) (by decide) ub) fun u' ⟨ck, cb, cv⟩ => ?_
  have uk : Op base X2 s u' := ⟨uk.1.trans ck.1, uk.2.trans ck.2⟩
  have uv : VG.Proof.X448.AArch64.F u'.mem base X2 = E s.mem base 1 * E s.mem base 21 :=
    cv.trans uv
  have us := hs.of_keeps uk.1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok us cb) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs vb ((vk.1 _ (by decide)).trans ((uk.1.1 _ (by decide)).trans hp))
    (by intro j hj; rw [vk.2.2, uk.1.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : Saved base g w.mem :=
    ⟨(output_word wm (by decide) (by decide) hfar).trans svv.1,
      (output_word wm (by decide) (by decide) hfar).trans svv.2⟩
  refine WP.mono (restore_ok ws svw) fun t ⟨tb, tr, tm, tk⟩ => ?_
  refine ⟨tb, tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans (tk.mono ?_))), ?_, ?_⟩
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide
  · rw [tm]
    exact (((uk.2.whole (by decide)).trans (vm.whole (by decide))).frame.mono (by simp)).trans
      (wm.frame.mono (by simp))
  · rw [tm, wv, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.AArch64.Weak
