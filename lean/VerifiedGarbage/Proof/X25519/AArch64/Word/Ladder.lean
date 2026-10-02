import VerifiedGarbage.Proof.X25519.AArch64.Word.Step

/-! The 255 public-count ladder iterations and the final conditional swaps. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Spec.X25519 VG.Proof.X25519
open VG.Impl.Ed25519.AArch64 VG.Proof.Ed25519.AArch64

theorem setCounter_ok (s : State) (n : BitVec 16) :
    WP isa (.block [.movz .x .x19 n 0]) s fun t =>
      t.gpr .x19 = n.setWidth 64 ∧ Keeps [.x19] s t := by
  refine WP.block_cons_iff.mpr ⟨_, VG.Proof.X25519.AArch64.exec_movz, WP.block_nil ?_⟩
  exact ⟨RegUpd.gpr_write_self _ _ _ _, ⟨fun r hr =>
    RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr), rfl, rfl, rfl, rfl⟩⟩

def LInv (base : Addr) (s₀ : State) (k : Nat) (x1 : Fe) (n : Nat) (s : State) : Prop :=
  LoopKeep base s₀ s ∧ Good (env s.mem base) x1 (ladderAfter k x1 n) ∧
  s.gpr .x19 = BitVec.ofNat 64 n ∧ word s.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 n).swap

theorem ladder_ok {base : Addr} {s : State} {k : Nat} {x1 : Fe} (hs : Scratch s base)
    (hg : Good (env s.mem base) x1 (init x1)) (hw : word s.mem base 768 = 0)
    (hb : ∀ i < 255, s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 (bit k i)) :
    WP isa VG.Impl.X25519.AArch64.Word.ladder s fun t =>
      LoopKeep base s t ∧ Good (env t.mem base) x1 (ladderAfter k x1 0) ∧
      word t.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 0).swap := by
  refine WP.seq (WP.mono (setCounter_ok s 255) fun a ⟨ac, ka⟩ => ?_)
  have kla : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  refine WP.loop (M := isa) (fun n t => 1 ≤ n ∧ n ≤ 255 ∧ LInv base s k x1 n t)
    ?_ 255 a ⟨by decide, by decide, kla, by simpa [ka.mem, ladderAfter_255] using hg, ac,
      by rw [ka.mem, ladderAfter_255]; exact hw⟩
  intro n t ⟨h1, h255, kt, gt, ct, wt⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i+1 := ⟨n-1, by omega⟩
  refine WP.mono (step_ok (k := k) (kt.scratch hs) (by omega) gt
    (ladderAfter_swap_le _ _ (by omega)) ct wt (by rw [kt.bit (by omega)]; exact hb i (by omega)))
    fun u ⟨ku, gu, cu, wu⟩ => ?_
  have klu : LoopKeep base s u := kt.trans ku
  rw [← ladderAfter_step k x1 (by omega)] at gu
  have ws : word u.mem base 768 = BitVec.ofNat 64 (ladderAfter k x1 i).swap := by
    rw [ladderAfter_step k x1 (by omega)]
    exact wu
  have he : isa.eval (.nonzero .x .x19) u = some (decide (i ≠ 0)) := by
    simp only [eval, read_x, cu, counter_nonzero (by omega : i < 2^64)]
  by_cases hi : i=0
  · subst i; exact .inl ⟨by rw [he]; rfl, klu, gu, ws⟩
  · exact .inr ⟨by rw [he]; simp [hi], i, by omega, by omega, by omega, klu, gu, cu, ws⟩


theorem lastMask_ok {s : State} {sw : Nat} (hsw : sw ≤ 1)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 sw) :
    WP isa (.block [.movz .x .x10 0 0, .sub .x .x3 .x10 .x3]) s fun t =>
      t.gpr .x3 = VG.Proof.Ed25519.Word64.mask (sw == 1) ∧ Keeps [.x3,.x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.X25519.AArch64.exec_movz, VG.Proof.X25519.AArch64.exec_sub_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [h3]; exact VG.Proof.X25519.AArch64.maskB_of hsw
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem lastSwap_ok {base : Addr} {s : State} {x1 : Fe} {st : Ladder}
    (hs : Scratch s base) (hg : Good (env s.mem base) x1 st) (hsw : st.swap ≤ 1)
    (hw : word s.mem base 768 = BitVec.ofNat 64 st.swap) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.lastSwap) s fun t =>
      LoopKeep base s t ∧ env t.mem base 1 = (Spec.X25519.cswap st.swap st.x2 st.x3).1 ∧
      env t.mem base 2 = (Spec.X25519.cswap st.swap st.z2 st.z3).1 := by
  change WP isa (.block (([VG.Impl.Ed25519.AArch64.ld .x3 768] : List Instr) ++
    ([.movz .x .x10 0 0, .sub .x .x3 .x10 .x3] ++
    (VG.Impl.Ed25519.AArch64.cswap (offset 1) (offset 3) ++
    VG.Impl.Ed25519.AArch64.cswap (offset 2) (offset 4))))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (d := 768) (by decide) (by decide) .x3) fun a ⟨aw, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (lastMask_ok hsw (aw.trans hw)) fun b ⟨bm, kb⟩ => ?_
  have kab : LoopKeep base s b := (LoopKeep.of_keeps ka (by decide)).trans
    (LoopKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (swapField_ok (kab.scratch hs) 1 3 (by decide) bm) fun c ⟨kc, ec, mc⟩ => ?_
  have kac := kab.trans (LoopKeep.of_field kc)
  refine WP.mono (swapField_ok (kac.scratch hs) 2 4 (by decide) (mc.trans bm)) fun t ⟨kt, et, _⟩ => ?_
  refine ⟨kac.trans (LoopKeep.of_field kt), ?_, ?_⟩ <;>
    rw [et, ec, kb.mem, ka.mem] <;>
    obtain ⟨h0,h1,h2,h3,h4,h18⟩ := hg <;>
    by_cases hw : st.swap = 1 <;>
    simp [swapped, Spec.X25519.cswap, hw, h1, h2, h3, h4]

end VG.Proof.X25519.AArch64.Word
