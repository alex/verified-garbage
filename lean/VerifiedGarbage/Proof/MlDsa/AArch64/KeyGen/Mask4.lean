import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks

namespace VG.Proof.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Proof.MlKem.AArch64 (Only Keep MemTo wp_nil wp_movz wp_strb wp_ldrw wp_strw wp_addImm wp_subImm
  count_loop)
open VG.Spec.MlDsa (coeffAt)
open VG.Spec.Sha3 (bytesAt)

theorem coeffAt_writeW32_4 (m : Mem) (q : Addr) {i j : Nat} (hi : i < 1024) (hj : j < 1024) (v : BitVec 32) :
    coeffAt (m.writeW (q + BitVec.ofNat 64 (4 * j)) v) q i = if j = i then v else coeffAt m q i := by
  unfold coeffAt
  split
  · subst j; exact Mem.readW_writeW_self32 m _ v
  · exact Mem.readW_writeW_sep (Offset.sep q (by omega) (by omega) (by omega)) (by decide)

theorem ofNat4_sub1 {i : Nat} (h : i < 1024) : BitVec.ofNat 64 (1024 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (1024 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem mask4_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State} (L : Lay S rbs wbs s) {a : Ptr}
    (hw : inB wbs a 4096 = true) (hin : inB (rbs ++ wbs) a 4096 = true)
    (hr : (s.gpr .x0).setWidth 32 = 0 ∨ (s.gpr .x0).setWidth 32 = 1) :
    WP isa (mask4 a) s fun s' => PPostB S s s' [(a, 4096)] ∧ Keep [.x1, .x2, .x8, .x9] s s' ∧
      ∀ i < 1024, coeffAt s'.mem (pa s a) i =
        if (s.gpr .x0).setWidth 32 = 1 then coeffAt s.mem (pa s a) i else 0 := by
  have hW : InRegions s.wr (pa s a) 4096 := L.inW hw
  have hn : (pa s a).toNat + 4096 ≤ 2 ^ 64 := L.nwp hin
  have hb : a.1 ∈ keptRegs := L.ptrBs hin
  have h1 : a.1 ≠ .x1 := by intro e; rw [e] at hb; revert hb; decide
  have h8 : a.1 ≠ .x8 := by intro e; rw [e] at hb; revert hb; decide
  unfold mask4
  refine WP.seq ?_
  refine wp_movz fun s₁ h₁ e₁ => wp_sub32 fun s₂ h₂ e₂ => lea_ok h1.symm a.2 fun s₃ h₃ e₃ =>
    wp_movz fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ : Keep [.x1, .x2, .x8, .x9] s s₄ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).mono (by simp)
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have x8 : s₄.gpr .x8 = BitVec.setWidth 64 (BitVec.setWidth 32 (0 : BitVec 64) - (s.gpr .x0).setWidth 32) := by
    rw [h₄.get .x8, h₃.get .x8, e₂, e₁, h₁.get .x0]; rfl
  have x1 : s₄.gpr .x1 = pa s a := by
    rw [h₄.get .x1, e₃, h₂.get a.1 (by simpa using h8), h₁.get a.1 (by simpa using h8)]
  refine WP.mono (count_loop (cr := .x2) (n := 1024) (by decide) (fun i s' =>
      s'.gpr .x1 = pa s a + BitVec.ofNat 64 (4 * i) ∧ s'.gpr .x2 = BitVec.ofNat 64 (1024 - i) ∧
      s'.gpr .x8 = s₄.gpr .x8 ∧ Keep [.x1, .x2, .x8, .x9] s s' ∧ Frame [⟨pa s a, 4096⟩] s.mem s'.mem ∧
      ∀ j < 1024, coeffAt s'.mem (pa s a) j =
        if j < i then coeffAt s.mem (pa s a) j &&& (s₄.gpr .x8).setWidth 32 else coeffAt s.mem (pa s a) j)
    (fun i hi s' ⟨e1, e2, e8, kk, hf, hc⟩ => ?_)
    ⟨by rw [x1, Nat.mul_zero, BitVec.add_zero], by rw [e₄]; rfl, rfl, k₄, by rw [m₄]; exact Frame.refl _ _,
      fun j _ => by rw [Proof.MlDsa.KeyGen.ifn (Nat.not_lt_zero j), m₄]⟩)
    fun s' ⟨_, _, _, kk, hf, hc⟩ => ⟨postB_of_keep kk (by decide) hf, kk, fun j hj => ?_⟩
  · have hc4 : (⟨pa s a, 4096⟩ : Region).Contains (pa s a + BitVec.ofNat 64 (4 * i)) 4 :=
      Offset.contains_base _ (by omega) (by omega)
    have hinw : InRegions s'.wr (s'.gpr .x1) 4 := by
      rw [kk.wr, e1]; exact inRegions_sub hW (by omega) (by omega)
    have hin0 : InRegions (s'.rd ++ s'.wr) (s'.gpr .x1) 4 := VG.Proof.MlKem.AArch64.in_rd_wr hinw
    refine WP.mono (maskBody_ok s' hin0 hinw) fun s'' ⟨⟨hm, e1', e2'⟩, k'⟩ => ⟨⟨?_, ?_, by rw [k'.get .x8, e8],
      (kk.trans k').mono (by simp), ?_, fun j hj => ?_⟩, ?_⟩
    · rw [e1', e1, off_add4]
    · rw [e2', e2, ofNat4_sub1 hi]
    · rw [hm, e1]; exact hf.writeW (List.mem_singleton_self _) _ hc4
    · rw [hm, e1, coeffAt_writeW32_4 _ _ hj (by omega), e8]
      by_cases e : i = j
      · subst e
        rw [Proof.MlDsa.KeyGen.ifp rfl, Proof.MlDsa.KeyGen.ifp (Nat.lt_succ_self _)]
        have := hc i hj
        rw [Proof.MlDsa.KeyGen.ifn (Nat.lt_irrefl _)] at this
        rw [← this]; rfl
      · rw [Proof.MlDsa.KeyGen.ifn e, hc j hj]
        by_cases hji : j < i
        · rw [Proof.MlDsa.KeyGen.ifp hji, Proof.MlDsa.KeyGen.ifp (by omega)]
        · rw [Proof.MlDsa.KeyGen.ifn hji, Proof.MlDsa.KeyGen.ifn (by omega)]
    · rw [e2', e2, ofNat4_sub1 hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [hc j hj, Proof.MlDsa.KeyGen.ifp hj, x8, and_mask hr]


end VG.Proof.MlDsa.AArch64.KeyGen
