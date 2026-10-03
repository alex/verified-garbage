import VerifiedGarbage.Proof.X448.X86.Restore
import VerifiedGarbage.Proof.X448.X86.Setup
import VerifiedGarbage.Proof.X448.X86.Output
import VerifiedGarbage.Proof.X448.X86.Freeze

/-!
# X448 on x86 (32-bit): the result and restored registers

The final multiplication, canonical reduction and encoding produce the affine
coordinate. The four callee-saved registers are then restored from the
disjoint working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

def finishRegs : List Reg := [.eax, .ebx, .ecx, .edx, .ebp, .esi, .edi]

theorem finish_ok {s₀ s : State} (pre : Pre s₀)
    (hsp : s.gpr .esp = s₀.gpr .esp) (hr : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {base : Addr} (hbase : (arg s₀ 3).setWidth 64 = base)
    (hm : Outside base 0 8192 s₀.mem s.mem)
    (hs : Scr s base) (hb : BoundedEnv s.mem base)
    (hfar : ∀ j < 8192, 56 ≤ ofs ((arg s₀ 0).setWidth 64) (off base j))
    (sv : Saved base s₀.gpr s.mem) :
    WP isa finish s fun t =>
      (∀ p ∈ savedSlots, t.gpr p.1 = s₀.gpr p.1) ∧ Keeps finishRegs s t ∧
      Frame [⟨base, 8192⟩, outR s₀] s.mem t.mem ∧
      Spec.X448.bytesAt t.mem ((arg s₀ 0).setWidth 64) 56 =
        Spec.X448.encodeUCoordinate (E s.mem base 1 * E s.mem base 21) := by
  refine WP.seq (WP.mono (mul_ok hs (o := X2) (a := X2) (b := T7) (by decide) (by decide)
    (by decide) (hb 1) (hb 21)) fun u ⟨uk, ub, uv⟩ => ?_)
  have us := hs.of_keeps uk.1 (by decide)
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (freeze_ok us ub) fun v ⟨vb, vv, vm, vk⟩ => ?_
  have vs := us.of_keeps vk (by decide)
  have frames := (uk.2.whole (by decide)).trans (vm.whole (by decide))
  have frame0 := hm.trans frames
  have ksv := uk.1.then vk
  have hvsp : v.gpr .esp = s₀.gpr .esp := (ksv.1 _ (by decide)).trans hsp
  have hvrd : v.rd = s₀.rd := ksv.2.1.trans hr
  have hvwr : v.wr = s₀.wr := ksv.2.2.trans hwr
  refine loadArg_ok pre hvsp hvrd hvwr (hbase ▸ frame0) (by decide : 0 < 4) fun v' hv => ?_
  have vs' := vs.of_upd hv (by decide)
  change WP isa (.block ((List.range 28).flatMap packLimb ++ restore)) v' _
  rw [WP.block_append_iff]
  refine WP.mono (output_ok vs' (hv.mem ▸ vb) (by rw [hv.gpr])
    (by rw [hv.gpr]; exact pre.out_fit)
    (by intro j hj; rw [hv.wr, hvwr]; exact ⟨outR s₀, pre.out_in,
      Offset.contains_base _ (by omega) (by omega)⟩) hfar) fun w ⟨wv, wm, wk⟩ => ?_
  have ws := vs'.of_keeps wk (by decide)
  have svv := (sv.field uk.2 (by decide)).field vm (by decide)
  have svw : Saved base s₀.gpr w.mem := svv.of_readW fun p hp => by
    have := savedSlots_bound p hp
    rw [← hv.mem]; exact output_word wm (by decide) (by omega) hfar
  refine WP.mono (restore_ok ws svw) fun t ⟨tr, tm, tk⟩ => ?_
  refine ⟨tr, (uk.1.mono ?_).trans ((vk.mono ?_).trans ((hv.rest (by decide)).trans ((wk.mono ?_).trans (tk.mono ?_)))), ?_, ?_⟩
  · intro r hr; simp only [clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [workRegs, clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [clob, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr; simp only [restoreRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [tm]
    rw [hv.mem] at wm
    exact (frames.frame.mono (by simp)).trans (wm.frame.mono (by simp [outR]))
  · rw [tm, wv, hv.mem, vv, encodeUCoordinate_eq]
    refine congrArg (VG.Proof.X25519.leBytes 56) ?_
    exact congrArg Fin.val uv

end VG.Proof.X448.X86
