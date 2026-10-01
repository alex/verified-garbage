import VerifiedGarbage.Proof.X448.Arm.Restore
import VerifiedGarbage.Proof.X448.Arm.Setup
import VerifiedGarbage.Proof.X448.Arm.Output
import VerifiedGarbage.Proof.X448.Arm.Freeze

/-!
# X448 on ARMv7: the result and restored registers

Untrusted: everything here is checked by Lean. The final multiplication,
canonical reduction and encoding produce the affine coordinate. The eight
callee-saved registers are then restored from the disjoint working space.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm

theorem Outside.frame {base : Addr} {n : Nat} {m m' : Mem} (h : Outside base 0 n m m') :
    Frame [⟨base, n⟩] m m' := fun x hx => h x (Or.inr (by
  have := hx _ (List.mem_singleton_self _)
  simp only [Region.Contains] at this
  change 0 + n ≤ (x - base).toNat
  omega))

theorem FieldMem.whole {base : Addr} {o : Nat} {m m' : Mem} (h : FieldMem base o m m')
    (ho : o + 112 ≤ 8192) : Outside base 0 8192 m m' := fun p hp =>
  h p (by omega) (by simp only [ACC]; omega)

theorem Outside2.whole {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : Outside2 base x nx y ny m m') (hx : x + nx ≤ 8192) (hy : y + ny ≤ 8192) :
    Outside base 0 8192 m m' := fun p hp => h p (by omega) (by omega)

theorem Saved.field {base : Addr} {g : Reg → BitVec 32} {m m' : Mem} (h : Saved base g m)
    {o : Nat} (hm : FieldMem base o m m') (ho : 32 ≤ o) : Saved base g m' := by
  intro i hi
  exact (hm.word (Or.inl (by omega)) (by simp only [ACC]; omega)).trans (h i hi)

def finishRegs : List Reg := saved ++ workRegs

theorem finish_ok {s : State} {base p : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hp : State.addr (s.gpr .r12) = p)
    (hfit : (s.gpr .r12).toNat + 56 ≤ 2 ^ 32) (hw : ∀ j < 56, InRegions s.wr (off p j) 1)
    (hfar : ∀ j < 8192, 56 ≤ ofs p (off base j)) {g : Reg → BitVec 32} (sv : Saved base g s.mem) :
    WP isa finish s fun t =>
      (∀ i < 8, t.gpr (saved[i]!) = g (saved[i]!)) ∧ Keeps finishRegs s t ∧
      Frame [⟨base, 8192⟩, ⟨p, 56⟩] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem p 56 = Spec.X448.encodeUCoordinate (E s.mem base 1 * E s.mem base 21) := by
  refine WP.seq (WP.mono (mul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.1 (by decide)
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (output_ok (p := p) vs vb (by rw [vk.1 _ (by decide), uk.1.1 _ (by decide)]; exact hp)
    (by rw [vk.1 _ (by decide), uk.1.1 _ (by decide)]; exact hfit)
    (by intro j hj; rw [vk.2.2, uk.1.2.2]; exact hw j hj) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : Saved base g w.mem := by
    intro i hi
    exact (output_word wm (by decide) (by omega) hfar).trans (svv i hi)
  refine WP.mono (restore_ok ws svw) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((wk.mono ?_).trans (tk.mono ?_))), ?_, ?_⟩
  · intro r hr; exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_append_right _ hr
  · intro r hr; exact List.mem_append_right _ (List.mem_cons_of_mem _ hr)
  · intro r hr; exact List.mem_append_left _ hr
  · rw [tm]
    exact (((uk.2.whole (by decide)).trans (vm.whole (by decide))).frame.mono (by simp)).trans
      (wm.frame.mono (by simp))
  · rw [tm, wv, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.Arm
