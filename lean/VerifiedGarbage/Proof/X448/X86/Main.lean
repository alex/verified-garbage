import VerifiedGarbage.Proof.X448.X86.BitsInput
import VerifiedGarbage.Proof.X448.X86.Finish
import VerifiedGarbage.Proof.X448.X86.Ladder
import VerifiedGarbage.Proof.X448.X86.FinalSwap
import VerifiedGarbage.Proof.X448.X86.Inv
import VerifiedGarbage.Spec.X448.Contract
import VerifiedGarbage.TCB.X86.Target

/-!
# X448 on x86 (32-bit): the whole function

Untrusted: everything here is checked by Lean. The contract the proof is
written against (the facts of `Spec.X448.x448Contract` it uses, stated
for x86 (32-bit)), and the correctness of `vg_x448` against it: every write is in
the working space but the result's, so the arguments are read unchanged, the
callee-saved registers restored from the working space, and the return
address kept.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86 VG.Proof.X448

/-- A byte of a region disjoint from the working space is beyond it. -/
theorem far {base p : Addr} {n : Nat} (hd : (⟨p, n⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < n) (hn : n ≤ 2 ^ 64) : 8192 ≤ ofs base (p + BitVec.ofNat 64 i) := by
  refine Nat.le_of_not_lt fun h => hd _ (Offset.contains_base p (d := i) (n := 1) (k := n) (by omega) (by omega)) ?_
  simp only [Region.Contains]; simp only [ofs] at h; omega

theorem bytesAt_outside {base p : Addr} {m m' : Mem} (h : Outside base 0 8192 m m')
    (hp : ∀ i < 56, 8192 ≤ ofs base (p + BitVec.ofNat 64 i)) :
    Spec.X448.bytesAt m' p 56 = Spec.X448.bytesAt m p 56 := by
  simp only [Spec.X448.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  simp only [List.mem_range] at hi
  exact hp i hi

theorem far_output {base p : Addr} (hd : (⟨p, 56⟩ : Region).Disjoint ⟨base, 8192⟩) {i : Nat}
    (hi : i < 8192) : 56 ≤ ofs p (off base i) := by
  refine Nat.le_of_not_lt fun h => hd _ ?_ (Offset.contains_base base (d := i) (n := 1) (k := 8192) (by omega) (by omega))
  simp only [Region.Contains]
  change ofs p (off base i) + 1 ≤ 56
  omega

theorem E_outside {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') (i : Index)
    (hi : slot i.val + 112 ≤ o ∨ o + n ≤ slot i.val) : E m' base i = E m base i := by
  simp only [E, F]
  rw [h.fe hi (by have := i.isLt; simp only [slot]; omega)]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa x448 s₀ fun s' => abiPreserved s₀ s' ∧ Proof.X448.x448X86.post s₀ s' := by
  obtain ⟨base, hbase⟩ : ∃ b, (arg s₀ 3).setWidth 64 = b := ⟨_, rfl⟩
  have hr : ∀ j < 56, InRegions (s₀.rd ++ s₀.wr) (off ((arg s₀ 2).setWidth 64) j) 1 := fun j hj =>
    ⟨pointR s₀, by rw [hp.rd]; simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hd : ∀ j < 56, 8192 ≤ ofs base (off ((arg s₀ 2).setWidth 64) j) :=
    fun j hj => far (hbase ▸ hp.point_sc) hj (by decide)
  have kd : ∀ j < 56, 8192 ≤ ofs base (off ((arg s₀ 1).setWidth 64) j) :=
    fun j hj => far (hbase ▸ hp.scalar_sc) hj (by decide)
  rw [x448]
  refine WP.seq (WP.mono (setup_ok hp hbase rfl hr hd)
    fun s₁ ⟨hs₁, b₁, k₁, o₁, sv₁, x1₁, x2₁, z2₁, x3₁, z3₁, sw₁⟩ => ?_)
  refine WP.seq (WP.mono (bits_ok hp (k₁.1 _ (by decide)) k₁.2.1 k₁.2.2 hbase o₁ hs₁ kd)
    fun s₂ ⟨k₂, o₂, bits₂⟩ => ?_)
  have k02 := k₁.then k₂
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have sv₂ : Saved base s₀.gpr s₂.mem := by exact sv₁.outside o₂ (by decide)
  have e₂ : ∀ i : Index, E s₂.mem base i = E s₁.mem base i := by
    intro i; exact E_outside o₂ i (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
  have b₂ : BoundedEnv s₂.mem base := by
    intro i j hj
    rw [o₂.limbs (d := slot i.val) (Or.inl (by have := i.isLt; simp only [slot, BITS]; omega))
      (by have := i.isLt; simp only [slot]; omega) hj]
    exact b₁ i j hj
  have kb := bytesAt_outside o₁ kd
  refine WP.seq (WP.mono (ladder_ok (s₀ := s₂) (s := s₂)
    (k := Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 56))
    (u := toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 56)))
    (fun t ht => by rw [bits₂ t ht, kb])
    (fun s' hb hg hm hr hw => ⟨
      ⟨by rw [hg _ (by decide)]; exact hs₂.edi, hw ▸ hs₂.wr,
        by rw [hg _ (by decide)]; exact hs₂.nowrap⟩, hm ▸ b₂,
      ⟨fun r h => hg r (fun e => h (by subst r; exact List.mem_cons_self)), hr, hw⟩,
      hb, hm ▸ Outside2.refl _ _ _ _ _ _,
      by rw [hm, e₂ 0, x1₁], by rw [hm, e₂ 1, x2₁]; rfl,
      by rw [hm, e₂ 2, z2₁]; rfl, by rw [hm, e₂ 3, x3₁, x1₁]; rfl,
      by rw [hm, e₂ 4, z3₁]; rfl,
      by rw [hm, o₂.word (d := SWAP) (by decide) (by decide), sw₁]; rfl⟩)) fun s₄ L => ?_)
  refine WP.seq (WP.mono (lastSwap_ok L.scr L.bounded
    (by have := ladderAfter_swap_le
          (Spec.X448.decodeScalar448 (Spec.X448.bytesAt s₀.mem ((arg s₀ 1).setWidth 64) 56))
          (toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s₀.mem ((arg s₀ 2).setWidth 64) 56)))
          (n := 0) (by decide); omega) L.swap) fun s₅ ⟨k₅, b₅, e₅⟩ => ?_)
  have hs₅ := k₅.scr L.scr
  refine WP.seq (WP.mono (invert_ok hs₅ b₅) fun s₆ ⟨k₆, b₆, e₆⟩ => ?_)
  have k26 := L.regs.then (k₅.regs.then k₆.regs)
  have sv₆ := ((sv₂.outside2 L.mem (by decide) (by decide)).outside2 k₅.mem (by decide)
    (by decide)).outside2 k₆.mem (by decide) (by decide)
  have k06 := k02.then k26
  have o₆ := ((o₁.trans (o₂.mono (by decide) (by decide))).trans
    (L.mem.whole (by decide) (by decide))).trans
    ((k₅.mem.whole (by decide) (by decide)).trans (k₆.mem.whole (by decide) (by decide)))
  refine WP.mono (finish_ok hp (k06.1 _ (by decide)) k06.2.1 k06.2.2 hbase o₆ (k₆.scr hs₅) b₆
    (fun j hj => far_output (hbase ▸ hp.out_sc) hj) sv₆) fun s' ⟨restored, kf, fm, result⟩ => ?_
  have kall := k06.then kf
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro r hr
      simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact restored 0 (by decide)
      · exact restored 1 (by decide)
      · exact restored 2 (by decide)
      · exact restored 3 (by decide)
      · exact kall.1 _ (by decide)
    · have frame : Frame [scR (arg s₀ 3), outR s₀] s₀.mem s'.mem := by
        rw [← hbase] at fm o₆
        exact (o₆.frame.mono (by simp)).trans fm
      have ret : (retR s₀).Contains ((s₀.gpr .esp).setWidth 64) 4 := by
        simpa only [BitVec.add_zero] using
          Offset.contains_base ((s₀.gpr .esp).setWidth 64) (d := 0) (n := 4) (k := 4) (by decide) (by decide)
      exact frame.readW ret
        (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl; exact hp.ret_sc; exact hp.ret_out) (by decide)

  · change Spec.X448.bytesAt s'.mem ((arg s₀ 0).setWidth 64) 56 = _
    rw [result, x448_eq]
    apply congrArg Spec.X448.encodeUCoordinate
    rw [e₆, invEnv_x2, invEnv_eval, e₅]
    simp (config := {decide := true}) only [opSwap, Function.update_apply, ite_true, ite_false]
    rw [L.x2, L.x3, L.z2, L.z3, cswap_fst, cswap_fst]

end VG.Proof.X448.X86
