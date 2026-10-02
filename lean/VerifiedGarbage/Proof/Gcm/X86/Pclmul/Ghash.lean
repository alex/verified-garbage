import VerifiedGarbage.Proof.Gcm.X86.Pclmul.Body
import VerifiedGarbage.Proof.Gcm.X86.Pclmul.CT
import VerifiedGarbage.Proof.Gcm.X86.Ghash

namespace VG.Proof.Gcm.X86.Pclmul
open VG VG.X86 VG.X86.RegUpd
open VG.Proof.Gcm.X86 (GPre yP nBlk yR rR)
open VG.Impl.Gcm.X86.Pclmul (at_)

theorem blocks_ok {s₀ s : State} (hp : GPre s₀) (hi : Inv s₀ 0 s) (hn : 0 < nBlk s₀) :
    WP isa (.loop (.block Impl.Gcm.X86.Pclmul.body) .ne) s (Inv s₀ (nBlk s₀)) := by
  refine WP.loop (M := isa) (fun k s => ∃ i,
    k = nBlk s₀ - i ∧ i < nBlk s₀ ∧ Inv s₀ i s)
    (fun k s ⟨i, hk, hb, hs⟩ => WP.mono (body_ok hp hs hb) fun s' ⟨inv, z⟩ => ?_)
    (nBlk s₀) s ⟨0, rfl, hn, hi⟩
  by_cases hl : i + 1 = nBlk s₀
  · refine .inl ⟨by simp [X86.eval, z, hl], ?_⟩
    rw [hl] at inv; exact inv
  · exact .inr ⟨by simp [X86.eval, z]; omega,
      nBlk s₀ - (i + 1), by omega, i + 1, rfl, by omega, inv⟩

theorem epilogue_ok {s₀ s : State} (hp : GPre s₀) (hi : Inv s₀ (nBlk s₀) s) :
    WP isa (.block Impl.Gcm.X86.Pclmul.epilogue) s fun s' =>
      abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  have writable : InRegions s.wr ((yP s₀).setWidth 64) 16 := by
    rw [hi.env.wr, hp.wr]
    exact ⟨yR s₀, by simp, Region.contains_self _ _⟩
  apply WP.of_runBlock
  simp only [Impl.Gcm.X86.Pclmul.epilogue, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, State.store128, gpr_setXmm, wr_setXmm, State.ea, at_, hi.out, BitVec.add_zero, writable,
    ite_true, mem_setXmm, xmm_setXmm_self, hi.rev,
    Option.some.injEq, exists_eq_left']
  constructor
  · constructor
    · intro r hr
      exact hi.env.saved r hr
    · rw [hi.env.mem, Mem.readW_writeW_sep
        (hp.rY.sep (Region.contains_self _ _) (Region.contains_self _ _)) (by decide)]
  · change Spec.Gcm.blockAt (s.mem.writeW ((yP s₀).setWidth 64)
      (XBinOp.eval .pshufb (s.xmm .xmm2) VG.Proof.Gcm.X86.revMask)) ((yP s₀).setWidth 64) = _
    rw [Proof.Gcm.X86.blockAt_store, hi.acc]

theorem gh_correct (s₀ : State) (hp : GPre s₀) :
    WP isa Impl.Gcm.X86.Pclmul.ghash s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Gcm.ghashX86.post s₀ s' := by
  unfold Impl.Gcm.X86.Pclmul.ghash
  refine WP.seq (WP.mono (prologue_ok s₀ hp) fun s₁ ⟨hi, z⟩ => ?_)
  have loop : WP isa (.ite .e (.block []) (.loop (.block Impl.Gcm.X86.Pclmul.body) .ne))
      s₁ (Inv s₀ (nBlk s₀)) := by
    refine WP.ite (decide (nBlk s₀ = 0)) (by simp only [X86.eval, z]) ?_ ?_
    · intro h
      have hn : nBlk s₀ = 0 := of_decide_eq_true h
      rw [hn]; exact WP.block_nil hi
    · intro h
      have hn : 0 < nBlk s₀ := by
        have hne : nBlk s₀ ≠ 0 := of_decide_eq_false h
        omega
      exact blocks_ok hp hi hn
  exact WP.seq (WP.mono loop fun s₂ inv => epilogue_ok hp inv)

theorem ghash_correct (s : State) (hs : Proof.Gcm.ghashX86.pre s) :
    ∃ t s', Exec isa Impl.Gcm.X86.Pclmul.ghash s t s' ∧ abiPreserved s s' ∧
      Proof.Gcm.ghashX86.post s s' := gh_correct s (GPre.of hs)

theorem ghash_verified :
    Verified X86.target Impl.Gcm.X86.Pclmul.ghash (Spec.Gcm.ghashContract X86.abi) :=
  Verified.of_correct ghash_correct ghash_ct
    (by
      open VG.Proof.Gcm.X86 in
      have a0 : arg ghSat 0 = 0x1000 := by decide
      have a1 : arg VG.Proof.Gcm.X86.ghSat 1 = 0x2000 := by decide
      have a2 : arg VG.Proof.Gcm.X86.ghSat 2 = 0x3000 := by decide
      have a3 : arg VG.Proof.Gcm.X86.ghSat 3 = 0 := by decide
      have a4 : arg VG.Proof.Gcm.X86.ghSat 4 = 0x4000 := by decide
      have e : argAddr VG.Proof.Gcm.X86.ghSat 0 = 0x8004 := by decide
      have esp : VG.Proof.Gcm.X86.ghSat.gpr .esp = 0x8000 := rfl
      sig_implies [Spec.Gcm.ghashContract, Spec.Gcm.ghashSig, X86.abi, X86.argSlots,
        X86.argVal, X86.argBytes, Proof.Gcm.ghashX86]
        [a0, a1, a2, a3, a4, e, esp] using VG.Proof.Gcm.X86.ghSat)

end VG.Proof.Gcm.X86.Pclmul
