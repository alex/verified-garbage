import VerifiedGarbage.Proof.Ed448.X86_64.Verify.Hash
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLocal
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLit

/-!
# Ed448 verification on x86-64: the challenge and the equation

Between the frame's push and pop (`Ctx`): the call of
`vg_ed448_scalar_reduce`, which leaves the hash in the frame reduced modulo
`L` at `k` (`reduce_ok`), and that of `vg_ed448_verify_equation` on the
public key, the signature and `k`, which leaves its result in `rax`
(`equation_ok`), for any proof that it meets its contract (`EqOk`): only the
whole function's `Verified` imports that proof, and the group theory it
imports.
-/

namespace VG.Proof.Ed448.X86_64.Verify

open VG VG.X86_64 VG.Impl.Ed448.X86_64.Verify
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Spec.Sha3 (bytesAt)

theorem reduce_nosp : NoSp Impl.Ed448.X86_64.scalarReduce := by
  have : ((instrs Impl.Ed448.X86_64.scalarReduce).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem reduce_depth : Impl.Ed448.X86_64.scalarReduce.depth ≤ 1 := by lit_decide

theorem equation_nosp : NoSp Impl.Ed448.X86_64.verifyEquation := by
  have : ((instrs Impl.Ed448.X86_64.verifyEquation).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem equation_depth : Impl.Ed448.X86_64.verifyEquation.depth ≤ 1 := by lit_decide

/-- `vg_ed448_verify_equation` meets the contract its proof is written against, and the ABI. -/
abbrev EqOk : Prop := ∀ s, Proof.Ed448.X86_64.verifyEquationLocal.pre s →
  ∃ t s', Exec isa Impl.Ed448.X86_64.verifyEquation s t s' ∧ abiPreserved s s' ∧
    Proof.Ed448.X86_64.verifyEquationLocal.post s s'

/-- `vg_ed448_verify_equation` is constant time for that contract. -/
abbrev EqCT : Prop := ConstantTime isa Proof.Ed448.X86_64.verifyEquationLocal.pre
  Proof.Ed448.X86_64.verifyEquationLocal.pub Impl.Ed448.X86_64.verifyEquation

section
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- The return address of a call from the frame, apart from `scratch`. -/
theorem ret_x (hL : L.Ok) : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ L.SCR := by
  have := hL.stk_x (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega)
  simpa only [x0] using this

/-- `k`, apart from `scratch`. -/
theorem k_x' (hL : L.Ok) : Region.Disjoint ⟨L.K, 57⟩ L.SCR := by
  have := hL.stk_x (d := 152) (n := 57) (e := 0) (k := 8192) (by omega) (by omega)
  rw [K_eq]; simpa only [x0] using this

theorem ret_k : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.K, 57⟩ := by
  rw [K_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem ret_h : Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ ⟨L.H, 114⟩ := by
  rw [H_eq]; exact Offset.disjoint _ (by omega) (by omega) (by omega)

theorem ret_r (hL : L.Ok) {r : Region} (hr : L.STK.Disjoint r) :
    Region.Disjoint ⟨L.B + BitVec.ofNat 64 8, 8⟩ r :=
  hL.stk_r hr (by omega)

theorem sp_ce {t : State} (hc : Ctx L g mx m₀ t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rsp = L.B + BitVec.ofNat 64 8 := by
  rw [rsp_ce, hc.rsp, sp_sub8]

/-! ## `k` -/

/-- The arguments of `vg_ed448_scalar_reduce`. -/
abbrev redArgs : List Arg := [.sp fK, .sp fH, .slot fScr]

theorem reduce_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_scalar_reduce" Impl.Ed448.X86_64.scalarReduce redArgs) t fun t' =>
      Ctx L g mx m₀ t' ∧ Spec.Ed448.bytesAt t'.mem L.K 57 = Spec.Ed448.scalarReduce (bytesAt t.mem L.H 114) := by
  refine WP.seq (WP.mono (setArgs_ok redArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3⟩ := argsIn3 hA
  rw [hc.sp] at e1 e2
  rw [hc.slot, hc.pScr] at e3
  change t1.gpr .rdi = L.K at e1
  change t1.gpr .rsi = L.H at e2
  have g1 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have hpre : Proof.Ed448.X86_64.scalarReduceLocal.pre
      (t1.callEntry.withRegions [⟨L.H, 114⟩] [⟨L.K, 57⟩, L.SCR]) := by
    simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, g3, sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    refine ⟨trivial, trivial, ?_, ret_k, ret_x hL, k_x' hL, hL.nScr⟩
    have := hL.stk_x (d := 32) (n := 114) (e := 0) (k := 8192) (by omega) (by omega)
    rw [H_eq]; simpa only [x0] using this
  refine call_ok hL Proof.Ed448.X86_64.scalarReduce_ok reduce_nosp reduce_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.FR, by simp, within_off _ (by omega)⟩)
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [.inr (within_off _ (by omega)), .inl (within_self _)])
    fun s' hc' _ _ ⟨s₂, hm₂, _, hpost⟩ => ⟨hc', ?_⟩
  simp only [Proof.Ed448.X86_64.scalarReduceLocal, g1, g2, State.withRegions_mem, hm₂] at hpost
  rw [hpost]
  refine congrArg _ ?_
  change bytesAt t1.callEntry.mem L.H 114 = bytesAt t.mem L.H 114
  rw [hc1.ce_bytesAt ret_h (by decide), hm]

/-! ## The equation -/

/-- The arguments of `vg_ed448_verify_equation`. -/
abbrev eqArgs : List Arg := [.slot fPk, .slot fSig, .sp fK, .slot fScr]

theorem equation_ok (hv : EqOk) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (callA "vg_ed448_verify_equation" Impl.Ed448.X86_64.verifyEquation eqArgs) t fun t' =>
      Ctx L g mx m₀ t' ∧ t'.gpr .rax = if Spec.Ed448.verifyEquation (bytesAt m₀ L.pk 57) (bytesAt m₀ L.sig 114)
        (bytesAt t.mem L.K 57) then 1 else 0 := by
  refine WP.seq (WP.mono (setArgs_ok eqArgs (by decide) t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hA
  rw [hc.slot, hc.pPk] at e1
  rw [hc.slot, hc.pSig] at e2
  rw [hc.sp] at e3
  rw [hc.slot, hc.pScr] at e4
  change t1.gpr .rdx = L.K at e3
  have g1 := (gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rdi ≠ .rsp)).trans e1
  have g2 := (gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rsi ≠ .rsp)).trans e2
  have g3 := (gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rdx ≠ .rsp)).trans e3
  have g4 := (gpr_ce t1 [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR] (by decide : Reg.rcx ≠ .rsp)).trans e4
  have hpre : Proof.Ed448.X86_64.verifyEquationLocal.pre
      (t1.callEntry.withRegions [L.PK, L.SIG, ⟨L.K, 57⟩] [L.SCR]) := by
    simp only [Proof.Ed448.X86_64.verifyEquationLocal, g1, g2, g3, g4, sp_ce hc1, State.withRegions_rd,
      State.withRegions_wr]
    exact ⟨trivial, trivial, hL.xPk.symm, hL.xSig.symm, k_x' hL, ret_x hL, hL.nScr⟩
  refine call_ok hL hv equation_nosp equation_depth hc1 hpre
    (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨L.PK, List.mem_append_left _ hL.inPk, within_self _⟩
      · exact ⟨L.SIG, List.mem_append_left _ hL.inSig, within_self _⟩
      · exact ⟨L.FR, by simp, within_off _ (by omega)⟩)
    (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact .inl (within_self _))
    fun s' hc' _ _ ⟨s₂, _, hg₂, hpost⟩ => ⟨hc', ?_⟩
  simp only [Proof.Ed448.X86_64.verifyEquationLocal, g1, g2, g3, State.withRegions_mem] at hpost
  rw [← hg₂ _ (by decide), hpost]
  have ep : Spec.Ed448.bytesAt t1.callEntry.mem L.pk 57 = bytesAt m₀ L.pk 57 := by
    change bytesAt t1.callEntry.mem L.pk 57 = _
    rw [hc1.ce_bytesAt (ret_r hL hL.kPk) (by decide), hc1.bytesAt_eq hL.xPk hL.kPk (by decide)]
  have es : Spec.Ed448.bytesAt t1.callEntry.mem L.sig 114 = bytesAt m₀ L.sig 114 := by
    change bytesAt t1.callEntry.mem L.sig 114 = _
    rw [hc1.ce_bytesAt (ret_r hL hL.kSig) (by decide), hc1.bytesAt_eq hL.xSig hL.kSig (by decide)]
  have ek : Spec.Ed448.bytesAt t1.callEntry.mem L.K 57 = bytesAt t.mem L.K 57 := by
    change bytesAt t1.callEntry.mem L.K 57 = _
    rw [hc1.ce_bytesAt ret_k (by decide), hm]
  rw [ep, es, ek]

end

end VG.Proof.Ed448.X86_64.Verify
