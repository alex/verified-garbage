import VerifiedGarbage.Proof.X448.X86.MulLoop
import VerifiedGarbage.Proof.X448.X86.Reduce

/-!
# X448 on x86 (32-bit): field multiplication

Untrusted: everything here is checked by Lean. The row loop produces the
56 limbs of the product, which are folded and normalized modulo the prime.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.X86.mul o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  rw [Impl.X448.X86.mul, WP.seq_iff]
  refine WP.mono (mulPre_ok hs a b) fun t ht => ?_
  rw [WP.seq_iff]
  refine WP.mono (mulLoop_ok ha hb ab bb ht) fun u hu => ?_
  have uk := hu.regs
  have us := hu.scr
  let f := limbs u.mem base ACC
  have fb : ∀ i < 56, f i < radix := hu.lt
  have fv : valN f 56 = fe s.mem base a * fe s.mem base b := hu.val
  have um := hu.mem
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok us (fun _ _ => rfl) fb) fun v ⟨vf, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  refine WP.mono (normalize_ok vs ho vf (reduced_bound fb)) fun w ⟨wf, wm, wk⟩ => ?_
  have value : fe w.mem base o % Spec.X448.P = (fe s.mem base a * fe s.mem base b) % Spec.X448.P := by
    rw [show fe w.mem base o = valN (normalized (reduced f)) 28 from valN_congr wf,
      normalized_mod (reduced_bound fb), reduced_mod, fv]
  refine ⟨⟨?_, ?_⟩, ?_, toFe_mul value⟩
  · exact uk.trans ((vk.mono (by decide)).trans (wk.mono (by decide)))
  · exact (FieldMem.work um (by omega) (by omega)).trans
      ((FieldMem.work vm (by decide) (by decide)).trans wm)
  · intro i hi
    rw [wf i hi]
    exact digit_lt _ _

end VG.Proof.X448.X86
