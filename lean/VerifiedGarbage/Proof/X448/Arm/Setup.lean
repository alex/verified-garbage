import VerifiedGarbage.Proof.X448.Arm.Initial
import VerifiedGarbage.Proof.X448.Arm.DecodeAll
import VerifiedGarbage.Proof.X448.Arm.Save

/-!
# X448 on ARMv7: reading the arguments

Setup saves the callee-saved registers, decodes the coordinate, and
initializes the ladder.
-/

namespace VG.Proof.X448.Arm

open VG VG.Arm VG.Impl.X448.Arm VG.Proof.X448.Radix16

def setupRegs : List Reg := [.r3, .r4, .r12, .r0, .r6]

theorem setup_ok {s : State} {base p : Addr} (hc : State.addr (s.gpr .r3) = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : (s.gpr .r3).toNat + 8192 ≤ 2 ^ 32) (hp : State.addr (s.gpr .r2) = p) (hfit : (s.gpr .r2).toNat + 56 ≤ 2 ^ 32)
    (hr : ∀ j < 56, InRegions (s.rd ++ s.wr) (off p j) 1)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun t =>
      Scr t base ∧ BoundedEnv t.mem base ∧ t.gpr .r12 = s.gpr .r0 ∧ Keeps setupRegs s t ∧
      Outside base 0 8192 s.mem t.mem ∧ Saved base s.gpr t.mem ∧
      E t.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E t.mem base 1 = 1 ∧ E t.mem base 2 = 0 ∧
      E t.mem base 3 = E t.mem base 0 ∧ E t.mem base 4 = 1 ∧ word t.mem base SWAP = 0 := by
  change WP isa (.block (setupHead ++ ((List.range 28).flatMap decodeLimb ++ initSlots))) s _
  rw [WP.block_append_iff]
  refine WP.mono (setupHead_ok hc hw hn) fun t ⟨ts, tp, tv, tm, tk⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (decodeAll_ok ts (by rw [tk.1 _ (by decide)]; exact hp)
    (by rw [tk.1 _ (by decide)]; exact hfit)
    (by intro j hj; rw [tk.2.1, tk.2.2]; exact hr j hj) hd) fun u ⟨ux, uy, um, uk⟩ => ?_
  have ub0 : Bounded u.mem base X1 := by intro j hj; rw [ux j hj]; exact decoded_lt _ _ _
  have ub3 : Bounded u.mem base X3 := by intro j hj; rw [uy j hj]; exact decoded_lt _ _ _
  have uv0 : E u.mem base 0 = toFe (VG.Proof.X25519.leNum (Spec.X448.bytesAt t.mem p 56)) := by
    apply congrArg toFe
    exact (valN_congr ux).trans (decoded_val t.mem p 28).symm
  have uv3 : E u.mem base 3 = E u.mem base 0 := congrArg toFe ((valN_congr uy).trans (valN_congr ux).symm)
  have byte : Spec.X448.bytesAt t.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    apply List.map_congr_left
    intro j hj
    exact tm _ (Or.inr (Nat.le_trans (by decide) (hd j (List.mem_range.mp hj))))
  rw [byte] at uv0
  refine WP.mono (initSlots_ok (ts.of_keeps uk (by decide)) ub0 ub3)
    fun v ⟨vb, v0, v1, v2, v3, v4, vw, vm, vk⟩ => ?_
  refine ⟨(ts.of_keeps uk (by decide)).of_keeps vk (by decide), vb,
    (vk.1 _ (by decide)).trans ((uk.1 _ (by decide)).trans tp),
    (tk.mono ?_).trans ((uk.mono ?_).trans (vk.mono ?_)),
    (tm.mono (by decide) (by decide)).trans ?_,
    (tv.outside2 um (by decide) (by decide)).outside vm (by decide),
    ?_, v1, v2, v3.trans (uv3.trans v0.symm), v4, vw⟩
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  · intro r h; simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide
  · intro r h; simp only [List.mem_singleton] at h; subst r; decide
  · exact (show Outside base 0 8192 t.mem u.mem from fun q h =>
      um q (by simp only [X1, slot]; omega) (by simp only [X3, slot]; omega)).trans
      (vm.mono (by decide) (by decide))
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
    exact v0.trans uv0

end VG.Proof.X448.Arm
