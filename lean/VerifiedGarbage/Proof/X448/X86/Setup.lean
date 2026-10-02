import VerifiedGarbage.Proof.X448.X86.Initial
import VerifiedGarbage.Proof.X448.X86.DecodeAll
import VerifiedGarbage.Proof.X448.X86.Save

/-!
# X448 on x86 (32-bit): reading the arguments

Setup saves the callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448.Radix16

def setupRegs : List Reg := [.eax, .edx, .edi, .esi]

theorem setup_ok {s : State} (hp : Pre s) {base p : Addr}
    (hc : (arg s 3).setWidth 64 = base) (hpoint : (arg s 2).setWidth 64 = p)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ Keeps setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧
      E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E t.mem base 1 = 1 ∧ E t.mem base 2 = 0 ∧
      E t.mem base 3 = E t.mem base 0 ∧ E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  simp only [setup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (save_ok hp) fun t ⟨ts, tv, tm, tk⟩ => ?_
  refine loadArg_ok hp (tk.1 _ (by decide)) tk.2.1 tk.2.2
    (tm.mono (by decide) (by decide)) (by decide : 2 < 4) fun t' ht => ?_
  rw [hc] at ts tv tm
  have ts' := ts.of_upd ht (by decide)
  have tm' : Outside base 0 16 s.mem t'.mem := by rw [ht.mem]; exact tm
  have tk' : Keeps setupRegs s t' := (tk.mono (by simp [setupRegs])).trans (ht.rest (by decide))
  change WP isa (.block ((List.range 28).flatMap decodeLimb ++ initSlots)) t' _
  rw [WP.block_append_iff]
  refine WP.mono (decodeAll_ok ts' (by rw [ht.gpr]; exact hpoint)
    (by rw [ht.gpr]; exact hp.point_fit)
    (by intro j hj; rw [tk'.2.1, tk'.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_lt _ _ _
  have ub3 : Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_lt _ _ _
  have uv0 : E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t'.mem p 56)) := by
    apply congrArg toFe
    exact (valN_congr ux).trans (decoded_val t'.mem p 28).symm
  have uv3 : E u.mem base 3 = E u.mem base 0 := congrArg toFe ((valN_congr uy).trans (valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t'.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm' _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (initSlots_ok (ts'.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts'.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    tk'.trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm'.mono (by decide) (by decide)).trans ?_,
    ((show Saved base s.gpr t'.mem from ht.mem ▸ tv).outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show Outside base 0 8192 t'.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega) (by simp only [X3, slot]; omega)).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.X86
