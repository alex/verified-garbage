import VerifiedGarbage.Proof.X448.Arm.Iter

/-!
# X448 on ARMv7: the final ladder swap

Untrusted: everything here is checked by Lean. The last swap bit selects
the coordinates that are converted back to affine form.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm
open VG.Proof.X25519.Arm (wp_mov op2_imm wp_dp op2_reg)

theorem mask_of : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block [ld .r2 SWAP, .mov .r5 (.imm 0), .dp .sub .r5 .r5 (.reg .r2)]) s
      fun t => t.gpr .r5 = mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ Keeps [.r2, .r5] s t := by
  refine load_ok hs (by decide) fun s1 h1 => ?_
  refine wp_mov (op2_imm (by decide)) fun s2 h2 => ?_
  refine wp_dp (op2_reg _ _) fun s3 h3 => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .r5 - s2.gpr .r2 = _
    rw [h2.gpr, h2.other .r2 (by decide), h1.gpr, hw]
    exact mask_of sw hsw
  · rw [h3.mem, h2.mem, h1.mem]
  · exact rest_keeps ((h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide))))

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block lastSwap) s fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = opSwap 2 4 (decide (sw = 1)) (opSwap 1 3 (decide (sw = 1)) (E s.mem base)) := by
  rw [lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  refine WP.mono (swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.Arm
