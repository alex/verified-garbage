import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyCall
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCorrect

/-!
# ML-DSA on x86-64, `verify_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageContract p X86_64.abi 112`, `verifyMessage n c p` returns 2 if
the context string is longer than 255 bytes; otherwise it computes
`tr = H(pk, 64)`, then `μ` of the formatted message, and calls the
verification function on `μ` `c`, which gives `ML-DSA.Verify_internal` of
the formatted message (`verifyMessage_wp`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- `scratch` to `r11`, 0 to `rax`. -/
theorem verifyMov_ok {p : Params} {s s1 : State} (h : VPre p s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r11 (.mem (stk 8)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r11 = stackArg s 0 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧ s2.mxcsr = s1.mxcsr) ∧
        Keep [.r11, .rax] s1 s2 := by
  have h8 : InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 8) 8 := by
    refine ⟨vArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← stackArgAddr0]
    exact Region.contains_self _ _
  refine WP.keep _ ?_ (by decide)
  xrun [ea_stk, h8, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl⟩

theorem cs_tmpV : ∀ r ∈ calleeSaved, r ∉ [Reg.r11, .rax] := by decide

/-- The arguments of `verifyRegs`, pushed. -/
theorem verifyRegs_vals {p : Params} {s s2 : State} (hk : ∀ r, r ∉ [Reg.r11, .rax] → s2.gpr r = s.gpr r)
    (h11 : s2.gpr .r11 = stackArg s 0) (hax : s2.gpr .rax = 0) :
    ∀ j (hj : j < 9), s2.gpr (verifyRegs[j]'(by simp [verifyRegs]; omega)) =
      (vlay p s).vals[j]'(by simp [Lay.vals]; omega) := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [verifyRegs, Lay.vals, vlay, List.getElem_cons_zero, List.getElem_cons_succ, h11, hax] <;>
    exact hk _ (by decide)

theorem verifyMessage_wp {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params)
    {s : State} (hpre : (verifyMessageContract p X86_64.abi 112).pre s) :
    WP isa (verifyMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageContract p X86_64.abi 112).post s s' := by
  have h := vPre_of hpre
  unfold verifyMessage top
  refine WP.seq (WP.mono (cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .r8).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine wp_ite_t hc1 (WP.seq (WP.mono (verifyMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h11, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := vlay_ok hp h h8
    have hg2 : ∀ r, r ∉ [Reg.r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (vlay p s).B + BitVec.ofNat 64 112 := by
      rw [hg2 _ (by decide), vlay_B]
    have hn : 8 * verifyRegs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide)]; have := h.sp; simp only [verifyRegs, List.length_cons, List.length_nil]; omega
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    refine WP.seq (WP.mono (entry_ok hL rfl (by decide) hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1)
      (verifyRegs_vals hg2 h11 hax) (hg2 _ (by decide)))
      fun t ⟨hc, htw, htsp⟩ => ?_)
    have hE := oE_lt hp
    have hk : (vlay p s).keyLen = p.pkLen := rfl
    refine WP.seq (WP.mono (trHash_ok hL rfl hk hc) fun t₁ ⟨hc₁, _, htr⟩ => ?_)
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    refine WP.seq (WP.mono (muHash_ok hL rfl hc₁ (tr := aMu p)
      (by simp [Arg.ok, Impl.MlDsa.X86_64.Message.aMu, fScr]; omega)
      (fun t' hc' => hc'.aMu p rfl) ⟨R, by simp [hR], hw⟩ st_mu.symm mu_ks (k_mu hL))
      fun t₂ ⟨hc₂, _, hμ⟩ => ?_)
    have F : VFacts p (vlay p s) := VOk.facts ⟨s, h, h8, rfl, rfl⟩
    refine WP.mono (verifyCall_ok hV hp hL F hc₂) fun s' ⟨hrd', hwr', hsp', hcs', hx', hf', hq⟩ => ?_
    have hm₀ : s2.mem = s.mem := hm2
    refine ⟨by rw [hsp', hc₂.rsp, ← htsp, hc.rsp], by rw [hwr', hc₂.wr, ← htw, hc.wr], ?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hsp', hc₂.rsp, Lay.SP, add_add, show 40 + 8 * verifyRegs.length = 112 from rfl, vlay_B]
        · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hcs' r hr, hc₂.cs r hr hr', hg2 r (cs_tmpV r hr)]
      · have eR : rRet s = ⟨(vlay p s).B + BitVec.ofNat 64 112, 8⟩ := by rw [vlay_B]
        have dB : ∀ k, k ≤ 112 → (rRet s).Disjoint ⟨(vlay p s).B, k⟩ := fun k hk => by
          rw [eR]; exact Offset.disjoint_base _ hk (by have := hL.nB; omega)
        rw [popped_mem, hf'.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (scrV_sub p _)
            · exact dB 40 (by decide)) (by decide),
          hc₂.frame.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (vlay_X p s).sub
            · exact dB 112 (by decide)) (by decide), hm₀]
      · rw [popped_mxcsr, hx', hc₂.mx, hx2, hx1]
    · sig_post [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
        List.range.loop]
      rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [verifyInternal, messageRep, pkTr]
      have ek : bytesAt t₂.mem (vlay p s).key p.pkLen = bytesAt s.mem (s.gpr .rdi) p.pkLen := by
        rw [hc₂.bytesAt_eq (p := (vlay p s).key) (n := p.pkLen) hL.xKey hL.kKey (by have := h.nPk; omega), hm₀]; rfl
      have es : bytesAt t₂.mem (vlay p s).sig p.sigLen = bytesAt s.mem (s.gpr .r9) p.sigLen := by
        rw [hc₂.bytesAt_eq (p := (vlay p s).sig) (n := p.sigLen) (h.sigScr.symm.sub_left (vlay_X p s).sub) h.stkSig
          (by have := h.nSig; omega), hm₀]; rfl
      have hμ' := hμ
      rw [htr, hm₀] at hμ'
      simp only [Verify.res] at hq
      rw [ek, es, hμ'] at hq
      simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
      exact hq
  · rw [decide_eq_false h8] at hc1
    refine wp_ite_f hc1 ?_
    xrun [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · sig_post [verifyMessageContract, verifyMessageSig, X86_64.abi, X86_64.argRegs, List.range,
        List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega)]
      rfl

end VG.Proof.MlDsa.X86_64.Message
