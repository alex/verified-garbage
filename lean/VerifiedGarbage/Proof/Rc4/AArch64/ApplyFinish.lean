import VerifiedGarbage.Proof.Rc4.AArch64.ApplySetup

/-!
# The PRGA's finish

`finish_ok`: the table is stored back from its registers at base `B`, then
`i` and `j = (j - B) + B`, and the callee-saved vector registers are
restored.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

theorem far_row {y p : Addr} {o : Nat} (ho : o + 16 ≤ 256) (h : ¬ (y - p).toNat < 258) :
    ¬ (y - (p + BitVec.ofNat 64 o)).toNat < 16 := by
  rw [Offset.sub_add_eq, Offset.toNat_sub_ofNat, Nat.mod_eq_of_lt (a := o) (by omega)]
  have := (y - p).isLt
  rw [show 2 ^ 64 - o + (y - p).toNat = ((y - p).toNat - o) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem j_byte (K : BitVec 8) (B : Nat) :
    (((bc K).extractLsb' 0 32).setWidth 64 + BitVec.ofNat 64 B).setWidth 8 = K + bB B := by
  have hl := congrArg BitVec.toNat (low_byte K)
  have hx := ((bc K).extractLsb' 0 32).isLt
  simp only [BitVec.toNat_setWidth] at hl
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem low_setLane (v : BitVec 128) (a : BitVec 64) : (setLane v 64 0 a).extractLsb' 0 64 = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [setLane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
  simp (disch := omega) [hi, decide_eq_true]

theorem i_byte (x : BitVec 64) : (x.setWidth 32).setWidth 8 = x.setWidth 8 :=
  BitVec.setWidth_setWidth (by decide)

/-- `i` and `j = (j - B) + B`. -/
theorem indices_ok {a : State} {B : Nat} {J : BitVec 8} (h8 : a.gpr .x8 = BitVec.ofNat 64 B)
    (hp : InRegions a.wr (a.gpr .x0) 258) (hj : a.v (dq 0) = bc (J - bB B)) :
    WP isa (.block [.strb .x4 .x0 256, .umov .w .x6 (dq 0) 0, .add .x .x6 .x6 .x8,
      .strb .x6 .x0 257]) a fun b =>
      b.mem = (a.mem.write (a.gpr .x0 + 256#64) 1 ((a.gpr .x4).setWidth 8)).write
        (a.gpr .x0 + 257#64) 1 J ∧
      b.v = a.v ∧ (∀ g, g ≠ .x6 → b.gpr g = a.gpr g) ∧ b.rd = a.rd ∧ b.wr = a.wr ∧ b.sp = a.sp := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  rrun [State.store, h256, h257, hj, h8, i_byte, j_byte, BitVec.sub_add_cancel]
  refine ⟨fun g hg => ?_, ?_⟩
  · simp [hg]
  · simp [State.write]

theorem restore_ok (prga : Bool) (s : State) :
    WP isa (.block (restore prga)) s fun t =>
      (∀ p ∈ saved prga, (t.v p.1).extractLsb' 0 64 = s.gpr p.2) ∧
      (∀ v, (∀ p ∈ saved prga, p.1 ≠ v) → t.v v = s.v v) ∧
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  cases prga <;>
  · unfold restore saved
    rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil]
    refine ⟨fun p hp => ?_, fun v hv => ?_, by simp [State.setV]⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [negBase, low_setLane]
    · simp only [List.forall_mem_cons] at hv
      try simp only [negBase] at hv ⊢
      simp only [show ∀ a : VReg, (v = a) = (a = v) from fun a => propext eq_comm]
      simp [hv]

theorem finish_ok {u : State} {B : Nat} {T : Table} {I J : BitVec 8} (hB : B % 16 = 0)
    (h8 : u.gpr .x8 = BitVec.ofNat 64 B) (h9 : u.gpr .x9 = 255#64)
    (hp : InRegions u.wr (u.gpr .x0) 258) (hT : TableIn u B T)
    (hj : u.v (dq 0) = bc (J - bB B)) (h4 : (u.gpr .x4).setWidth 8 = I) :
    WP isa (.block applyFinish) u fun t =>
      contextAt t.mem (u.gpr .x0) = ⟨T, I, J⟩ ∧
      (∀ y, ¬ (y - u.gpr .x0).toNat < 258 → t.mem y = u.mem y) ∧
      (∀ p ∈ saved true, (t.v p.1).extractLsb' 0 64 = u.gpr p.2) ∧ t.v .v15 = u.v .v15 ∧
      t.rd = u.rd ∧ t.wr = u.wr ∧ t.sp = u.sp := by
  have h256w : InRegions u.wr (u.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hp
  unfold applyFinish
  rw [List.append_assoc, WP.block_append_iff, storeTable_eq]
  refine WP.mono (storeN_ok hB h8 h9 h256w (Nat.le_refl 16))
    fun a ⟨arow, aout, av, ag, ard, awr, asp⟩ => ?_
  have a0 : a.gpr .x0 = u.gpr .x0 := ag _ (by decide) (by decide)
  have a4 : a.gpr .x4 = u.gpr .x4 := ag _ (by decide) (by decide)
  have a8 : a.gpr .x8 = u.gpr .x8 := ag _ (by decide) (by decide)
  rw [WP.block_append_iff]
  have hpa : InRegions a.wr (a.gpr .x0) 258 := by rw [awr, a0]; exact hp
  refine WP.mono (indices_ok (J := J) (a8.trans h8) hpa (by rw [av]; exact hj))
    fun b ⟨bm, bv, bg, brd, bwr, bsp⟩ => ?_
  refine WP.mono (restore_ok true b) fun t ⟨tsv, tv, _, tm, trd, twr, tsp⟩ => ?_
  refine ⟨?_, fun y hy => ?_, fun p hp => ?_, ?_, ?_, ?_, ?_⟩
  · rw [tm, bm, a0, a4, h4, context_finish, stored_table hB hT arow]
  · have hne (d : Nat) (hd : d < 258) : y ≠ u.gpr .x0 + BitVec.ofNat 64 d := fun e => by
      rw [e, Offset.add_sub_cancel_left, BitVec.toNat_ofNat] at hy; omega
    rw [tm, bm, a0, write_byte, ite_eq_right (hne 257 (by decide)), write_byte,
      ite_eq_right (hne 256 (by decide))]
    exact aout y fun r _ => far_row (rowOff_le r hB) hy
  · obtain ⟨h6, h7⟩ := saved_ne p hp
    rw [tsv p hp, bg _ h6, ag _ h6 h7]
  · rw [tv _ (by decide), bv, av]
  · rw [trd, brd, ard]
  · rw [twr, bwr, awr]
  · rw [tsp, bsp, asp]

end VG.Proof.Rc4.AArch64
