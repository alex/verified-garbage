import VerifiedGarbage.Proof.MlKem.X86.NttLoop
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Contract

/-!
# ML-KEM on x86 (32-bit): the start of `vg_mlkem_ntt` and `vg_mlkem_inv_ntt`

Both load `scratch` into `eax` (`ld_piece`), store the zeta table there, point
`ebp` at zeta `z`, and store `f + 1024` in the argument slot of `scratch`
(`setup_piece`), leaving `MemOK` with the input polynomial.
-/

namespace VG.Proof.MlKem.X86.NttLoop

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Spec.MlKem

theorem Pre.of {s₀ : State} {stk : Nat} {t : Poly → Poly}
    (h : (inPlaceContract X86.abi t stk).pre s₀) (hs : stk = 16) : Pre s₀ := by
  subst hs
  sig_pre [inPlaceContract, inPlaceSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- After `ldScratch`. -/
structure S1 (s₀ : State) (s : State) : Prop where
  esp : s.gpr .esp = (P0 s₀).gpr .esp
  rd : s.rd = (P0 s₀).rd
  wr : s.wr = (P0 s₀).wr
  mem : s.mem = (P0 s₀).mem
  eax : s.gpr .eax = sP s₀

theorem ld_piece : Piece Pre Pub (fun s₀ s => s = P0 s₀) S1 (.block ldScratch) := by
  refine Piece.taint [.esp] (fun s₀ s hp e => ?_) (fun s₀ s₀' s s' _ _ hq e e' r hr => ?_)
    (by taint_decide)
  · subst e
    have fit := hp.sp'
    have a₁ := P0_argAddr s₀ 1
    have i₁ := P0_argIn (s₀ := s₀) (n := 2) (i := 1) (by omega) fit (by simp [hp.wr])
    have v₁ := P0_arg hp.sp (n := 2) (i := 1) (by omega) fit (by
      simpa [← hp.stk_eq] using hp.stk_a)
    simp only [Nat.mul_one, Nat.reduceAdd] at a₁
    apply WP.of_runBlock
    simp only [ldScratch, at_, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.ea,
      State.load32, State.setReg, Option.map_some, a₁, i₁, v₁, ite_true, Option.some.injEq,
      exists_eq_left']
    exact ⟨by simp, rfl, rfl, rfl, by simp⟩
  · simp only [List.mem_singleton] at hr
    subst hr
    rw [e, e', pub_esp hq]

theorem arg01_sep {s₀ : State} (hp : Pre s₀) : Mem.Sep (argAddr s₀ 0) 4 (argAddr s₀ 1) 4 := by
  have := hp.sp'
  intro x h₁ h₂
  simp only [argAddr, E0] at this h₁ h₂
  bv_omega

theorem setup_piece (z : Nat) {hh : Taint.Hint VG.X86.Taint.T}
    (ht : (VG.X86.taint.check (τr [.esp, .eax]) (.block (nttSetup z)) hh).isSome = true) :
    Piece Pre Pub S1 (fun s₀ s => LB s₀ (polyAt s₀.mem (fA s₀)) z s) (.block (nttSetup z)) := by
  refine Piece.taint [.esp, .eax] (fun s₀ s hp h => ?_) (fun s₀ s₀' s s' _ _ hq h h' r hr => ?_) ht
  · have fs := hp.s_fit
    have fit := hp.sp'
    rw [nttSetup]
    refine table_spec zetaTable (b := .eax) (by decide) (p := sA s₀) _ s _
      (fun k hk => by
        show (s.gpr .eax + BitVec.ofNat 32 (4 * k)).setWidth 64 = _
        rw [h.eax, ea_off (by omega)])
      (fun k hk => hp.in_s h.wr (by omega)) fun s₁ o₁ f₁ c₁ => ?_
    have esp₁ : s₁.gpr .esp = (P0 s₀).gpr .esp := by rw [o₁.gpr .esp (by decide), h.esp]
    have eax₁ : s₁.gpr .eax = sP s₀ := by rw [o₁.gpr .eax (by decide), h.eax]
    have wr₁ : s₁.wr = (P0 s₀).wr := o₁.wr.trans h.wr
    have rd₁ : s₁.rd = (P0 s₀).rd := o₁.rd.trans h.rd
    have a20 : (s₁.gpr .esp + BitVec.ofNat 32 20).setWidth 64 = argAddr s₀ 0 := by
      rw [esp₁]; exact P0_argAddr s₀ 0
    have a24 : (s₁.gpr .esp + BitVec.ofNat 32 24).setWidth 64 = argAddr s₀ 1 := by
      rw [esp₁]; exact P0_argAddr s₀ 1
    have in0 : InRegions (s₁.rd ++ s₁.wr) (argAddr s₀ 0) 4 := hp.in_a wr₁ (by decide)
    have in1 : InRegions s₁.wr (argAddr s₀ 1) 4 :=
      ⟨aR s₀, by rw [wr₁, P0_wr, hp.wr]; simp, hp.arg_in (by decide)⟩
    have hsa : ∀ r ∈ [polyRegion (sA s₀)], (⟨argAddr s₀ 0, 4⟩ : Region).Disjoint r := by
      simp only [List.mem_singleton, forall_eq]
      exact (hp.s_a.symm.sub_left fun x hx => by
        have := hp.arg_in (i := 0) (by decide)
        simp only [Region.Contains] at hx this ⊢; omega)
    have v0 : s₁.mem.readW (argAddr s₀ 0) 32 = fP s₀ := by
      rw [f₁.readW (Region.contains_self _ _) hsa (by decide), h.mem]
      exact P0_arg hp.sp (n := 2) (i := 0) (by omega) fit (by simpa [← hp.stk_eq] using hp.stk_a)
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
      readSrc, State.ea, at_, State.load32, State.store32, State.setReg, arithFlags, State.setFlags,
      Option.map_some, Option.bind_some, a20, a24, in0, in1, v0, ite_true, ite_false, Option.some.injEq,
      exists_eq_left']
    have hs1 : Frame [polyRegion (sA s₀)] (P0 s₀).mem s₁.mem := h.mem ▸ f₁
    refine ⟨by simp [esp₁], rd₁, wr₁, by simp [eax₁], ?_, ?_, ?_, ?_, ?_⟩
    · exact (hs1.mono fun r hr => by simp at hr ⊢; exact .inr (.inl hr)).writeW (by simp) _
        (hp.arg_in (by decide))
    · intro k hk
      rw [coeffAt_writeW_sep _ _ _ (hp.s_a.sep (coeff_contains _ (by rw [n_eq]; omega)) (hp.arg_in (by decide))),
        c₁ k hk]
      rfl
    · rw [Mem.readW_writeW_sep (arg01_sep hp) (by decide), v0]
    · exact Mem.readW_writeW_self32 _ _ _
    · have fr : Frame [frameR s₀, polyRegion (sA s₀), aR s₀] s₀.mem
          (s₁.mem.writeW (argAddr s₀ 1) (fP s₀ + 1024)) :=
        ((hp.P0_keep.mono (by simp)).trans (hs1.mono (by simp))).writeW (by simp) _ (hp.arg_in (by decide))
      refine polyIs_congr (fun k hk => bytes_frame fr (fun r hr => ?_) (by decide) k hk) ⟨hp.f_red, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [← hp.stk_eq]; exact hp.stk_f.symm
      · exact hp.f_s
      · exact hp.f_a
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [h.esp, h'.esp, pub_esp hq]
    · rw [h.eax, h'.eax, sP, sP, hq.2.2]

end VG.Proof.MlKem.X86.NttLoop
