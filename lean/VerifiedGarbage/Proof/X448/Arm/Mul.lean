import VerifiedGarbage.Proof.X448.Arm.MulLoop
import VerifiedGarbage.Proof.X448.Arm.Reduce

/-!
# X448 on ARMv7: field multiplication

Untrusted: everything here is checked by Lean. The row loop produces the
56 limbs of the product, which are folded and normalized modulo the prime.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

theorem frame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : Frame [⟨off base o, n⟩] m m') (hn : o + n ≤ 8192) : Outside base o n m m' := by
  intro x hx
  refine h x fun r hr hc => ?_
  rw [List.mem_singleton.mp hr] at hc
  change (x - off base o).toNat + 1 ≤ n at hc
  simp only [off] at hc
  have hi := (Offset.lt_iff x base (d := o) (n := n) (by omega)).mp (by omega)
  simp only [ofs] at hx
  omega

theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat}
    (ho : Slot o) (ha : Slot a) (hb : Slot b) (ab : Bounded s.mem base a) (bb : Bounded s.mem base b) :
    WP isa (Impl.X448.Arm.mul o a b) s fun t =>
      Op base o s t ∧ Bounded t.mem base o ∧ F t.mem base o = F s.mem base a * F s.mem base b := by
  let ptr := s.gpr .r0
  have pe : State.addr ptr = base := hs.r0
  have ctx : RowCtx ptr s := ⟨rfl, by change (s.gpr .r0).toNat + 4096 ≤ 2 ^ 32; have := hs.nowrap; omega,
    by rw [pe]; exact hs.wr⟩
  rw [Impl.X448.Arm.mul, WP.seq_iff]
  refine WP.mono (mulPre_ok (x := a) (y := b) ctx hs.mask) fun t ht => ?_
  rw [WP.seq_iff]
  refine WP.mono (mulLoop_ok ha hb (by rw [pe]; exact ab) (by rw [pe]; exact bb) ht) fun u hu => ?_
  have uk : Keeps clob s u := rest_keeps hu.rest
  have us := hs.of_keeps uk (by decide)
  let f := limbs u.mem base ACC
  have fb : ∀ i < 56, f i < radix := by
    intro i hi
    have := hu.lt i hi
    rw [pe] at this
    exact this
  have fv : valN f 56 = fe s.mem base a * fe s.mem base b := by
    have := hu.val
    rw [pe] at this
    exact this
  have um : Outside base ACC 224 s.mem u.mem := by
    have hf := hu.frame
    rw [pe] at hf
    exact frame_outside hf (by decide)
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

end VG.Proof.X448.Arm
