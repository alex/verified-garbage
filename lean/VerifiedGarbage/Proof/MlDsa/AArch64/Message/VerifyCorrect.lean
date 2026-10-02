import VerifiedGarbage.Proof.MlDsa.AArch64.Message.VerifyCall

/-!
# ML-DSA on AArch64, `verify_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageContract p AArch64.abi 16`, `verifyMessage v.callee n c p`
returns 2 if the context string is longer than 255 bytes; otherwise it
computes `tr = H(pk, 64)`, then `μ` of the formatted message, and calls the
verification function on `μ` `c`, which gives `ML-DSA.Verify_internal` of
the formatted message (`verifyMessage_wp`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only wp_nil wp_movz)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

theorem verifySaves_vals {p : Params} {s s1 : State} (o : Only [.x9] s s1) :
    ∀ j (hj : j < verifySaves.length), s1.gpr (verifySaves[j]'hj).1 = (vlay p s).vals.getD j 0 := by
  intro j hj
  have : j < 8 := hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [verifySaves, Lay.vals, vlay, List.getElem_cons_zero, List.getElem_cons_succ, List.getD_cons_zero,
      List.getD_cons_succ] <;> exact o.get _

theorem verifyMessage_wp (v : Proof.Sha3.AArch64.Permutation) {p : Params} {n : String} {c : Prog isa}
    (hV : VerifyFn p c) (hp : p ∈ params) {s : State} (hpre : (verifyMessageContract p AArch64.abi 16).pre s) :
    WP isa (verifyMessage v.callee n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageContract p AArch64.abi 16).post s s' := by
  have h := vPre_of hpre
  unfold verifyMessage top
  refine WP.seq (WP.mono (lsr_ok s) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .x4).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := vlay_ok hp h h8
    refine wp_ite_f hc1 (WP.seq (WP.mono (enter_ok hL rfl (by decide) rfl (o1.get .x6) (by rw [o1.sp]; rfl)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .x4) (verifySaves_vals o1) (by decide))
      fun t hc => ?_))
    refine WP.seq (WP.seq (WP.mono (trHash_ok v hL rfl hc) fun t₁ ⟨hc₁, htr⟩ => ?_))
    have hst : Region.Sub ⟨(vlay p s).ST, 200⟩ (vlay p s).XS := by
      have := Offset.sub_base (vlay p s).X (d := 0) (n := 200) (k := 1024) (by omega)
      simpa only [x0] using this
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    refine WP.seq (WP.mono (muHash_ok v hL hc₁ (tr := .off oMU) (by decide) rfl (fun t' hc' => hc'.off oMU)
      ⟨R, by simp [hR], hw⟩ st_mu.symm mu_ks (k_mu hL)) fun t₂ ⟨hc₂, hμ⟩ => ?_)
    refine WP.mono (verifyCall_ok hV hp h h8 hc₂) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun s'' ⟨hcs, hsp, hvs, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), hsp,
      fun r hr => (hvs r hr).trans (o1.vcs r hr)⟩, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₂.mem (s.gpr .x0) p.pkLen = bytesAt s.mem (s.gpr .x0) p.pkLen :=
      (hc₂.bytesAt_eq (p := (vlay p s).key) (n := p.pkLen) hL.xKey hL.kKey (by have := h.nPk; omega)).trans
        (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (s.gpr .x5) p.sigLen = bytesAt s.mem (s.gpr .x5) p.sigLen :=
      (hc₂.bytesAt_eq (p := (vlay p s).sig) (n := p.sigLen) (h.sigScr.symm.sub_left (vlay_X p s).sub) h.stkSig
        (by have := h.nSig; omega)).trans (by rw [hm₀]; rfl)
    have hμ' := hμ
    rw [show (vlay p s).X + BitVec.ofNat 64 oMU = (vlay p s).MU from rfl, htr, hm₀] at hμ'
    rw [ek, es, hμ'] at hq
    rw [hx0]
    simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (wp_movz fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp],
      fun r hr => by rw [o2.vcs r hr, o1.vcs r hr]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.x0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h9 : r ∉ [Reg.x9] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.get r h0, o1.get r h9]
    · sig_post [verifyMessageContract, verifyMessageSig, AArch64.abi, AArch64.argRegs, List.range,
        List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), e2]
      rfl

end VG.Proof.MlDsa.AArch64.Message
