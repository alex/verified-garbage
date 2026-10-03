import VerifiedGarbage.Proof.X448.X86.Iter

/-!
# X448 on x86 (32-bit): the final ladder swap

The last swap bit selects the coordinates that are converted back to affine
form.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

theorem mask_of : ∀ a < 2, (0 : BitVec 32) - BitVec.ofNat 32 a = mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 32 sw) :
    WP isa (.block [ld .ecx SWAP, .mov .ebx (.imm 0), .alu .sub .ebx (.reg .ecx)]) s
      fun t => t.gpr .ebx = mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ Keeps [.ecx, .ebx] s t := by
  refine load_ok hs (by decide) fun s1 h1 => ?_
  refine wp_mov rfl fun s2 h2 => ?_
  refine wp_alu (Or.inr (Or.inl rfl)) rfl fun s3 h3 _ => WP.block_nil ⟨?_, ?_, ?_⟩
  · rw [h3.gpr]
    change s2.gpr .ebx - s2.gpr .ecx = _
    rw [h2.gpr, h2.other .ecx (by decide), h1.gpr, hw]
    exact mask_of sw hsw
  · rw [h3.mem, h2.mem, h1.mem]
  · exact (h1.rest (by decide)).trans ((h2.rest (by decide)).trans (h3.rest (by decide)))

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

end VG.Proof.X448.X86
