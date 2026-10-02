import VerifiedGarbage.Proof.MlDsa.Arm.Message.VerifyCall
import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCorrect

/-!
# ML-DSA on ARMv7, `verify_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`verifyMessageContract p Arm.abi 36`, `verifyMessage n c p` returns 2 if
the context string is longer than 255 bytes; otherwise it computes
`tr = H(pk, 64)`, then `μ` of the formatted message, and calls the
verification function on `μ` `c`, which gives the result of
`ML-DSA.Verify_internal` on the formatted message (`verifyMessage_wp`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- The words on the stack of a state satisfying `VPre` are readable. -/
theorem VPre.args {p : Params} {s : State} (h : VPre p s) {o : Nat} (ho : o + 4 ≤ 12) :
    InRegions (s.rd ++ s.wr) (State.addr (s.sp + BitVec.ofNat 32 o)) 4 := by
  refine ⟨rArgs s 12, by simp [h.rd], ?_⟩
  simp only [rArgs, stackArgAddr0]
  rw [addr_add (by have := h.spA; omega)]
  exact Offset.contains_base _ ho (by omega)

theorem verifyMessage_wp {p : Params} {n : String} {c : Prog isa}
    (hV : VerifyFn p c) (hp : p ∈ params) {s : State} (hpre : (verifyMessageContract p Arm.abi 36).pre s) :
    WP isa (verifyMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (verifyMessageContract p Arm.abi 36).post s s' := by
  have h := vPre_of hpre
  unfold verifyMessage top
  refine WP.seq (WP.mono (chk_ok (h.args (by omega))) fun s1 ⟨o1, hc1⟩ => ?_)
  by_cases h8 : (stackArg s 0).toNat < 256
  · rw [decide_eq_false (by simpa using h8)] at hc1
    have hL := vlay_ok hp h h8
    have hs1 : ∀ o, o + 4 ≤ 12 → s1.mem.readW (State.addr (s1.sp + BitVec.ofNat 32 o)) 32 =
        s.mem.readW (State.addr (s.sp + BitVec.ofNat 32 o)) 32 := fun _ _ => by rw [o1.mem, o1.sp]
    refine wp_ite_f hc1 (WP.seq (WP.mono (enter_ok hL rfl (nA := 12) (by decide) (by omega) (o1.sp)
      (by rw [o1.rd]; rfl) (by rw [o1.wr]; rfl) (o1.get .r0) (o1.get .r1) (o1.get .r2) (o1.get .r3)
      (fun o ho => by rw [o1.rd, o1.wr, o1.sp]; exact h.args ho) (by rw [o1.sp]; exact h.spA)
      (by rw [o1.sp, ← stackArgAddr0]; exact h.scrArgs) (by omega)
      (by rw [hs1 8 (by omega)]; exact stackArg_eq s 2) (by decide) (fun j hj => by
        have hj4 : j < 4 := hj
        rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
        · exact (hs1 0 (by decide)).trans (stackArg_eq s 0)
        · exact (hs1 4 (by decide)).trans (stackArg_eq s 1)
        · exact (hs1 4 (by decide)).trans (stackArg_eq s 1)
        · exact (hs1 8 (by decide)).trans (stackArg_eq s 2))) fun t hc => ?_))
    refine WP.seq (WP.seq (WP.mono (trHash_ok hL rfl hc) fun t₁ ⟨hc₁, htr⟩ => ?_))
    have hmu := mu_eq hL
    have hfit : ((vlay p s).X32 + BitVec.ofNat 32 840).toNat + 64 ≤ 2 ^ 32 := by
      have := hL.x32_lt; rw [x32_toNat hL (by omega)]; omega
    obtain ⟨R, hR, hw⟩ := hL.covX (e := 840) (k := 64) (by omega)
    refine WP.seq (WP.mono (muHash_ok hL hc₁ (tr := .off oMU) (trp := (vlay p s).X32 + BitVec.ofNat 32 840)
      (by decide) rfl (fun t' hc' => hc'.off oMU) hfit
      (by rw [hmu]; exact ⟨R, by simp [hR], hw⟩) (by rw [hmu]; exact st_mu.symm) (by rw [hmu]; exact mu_ks)
      (by rw [hmu]; exact k_mu hL)) fun t₂ ⟨hc₂, hμ⟩ => ?_)
    refine WP.mono (verifyCall_ok hV hp h h8 hc₂) fun s' ⟨hf, hq⟩ => ?_
    refine WP.mono (leave_ok hL hf) fun s'' ⟨hcs, hsp, hm, hx0, _, _⟩ => ?_
    refine ⟨⟨fun r hr => by rw [hcs r hr]; exact o1.get r (fun e => by
        simp only [List.mem_singleton] at e; subst e; revert hr; decide), by rw [hsp]; rfl⟩, ?_⟩
    sig_post [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
    rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
    simp only [verifyInternal, messageRep, pkTr]
    have hm₀ : s1.mem = s.mem := o1.mem
    have ek : bytesAt t₂.mem (State.addr (s.gpr .r0)) p.pkLen = bytesAt s.mem (State.addr (s.gpr .r0)) p.pkLen :=
      (hc₂.bytesAt_eq (p := State.addr (vlay p s).key) (n := p.pkLen) hL.xKey hL.kKey
        (by have := h.nPk; omega)).trans (by rw [hm₀]; rfl)
    have es : bytesAt t₂.mem (State.addr (stackArg s 1)) p.sigLen =
        bytesAt s.mem (State.addr (stackArg s 1)) p.sigLen :=
      (hc₂.bytesAt_eq (p := State.addr (vlay p s).sig) (n := p.sigLen) h.sigScr.symm h.stkSig
        (by have := h.nSig; omega)).trans (by rw [hm₀]; rfl)
    have hμ' := hμ
    rw [hmu, htr, hm₀] at hμ'
    rw [ek, es, hμ'] at hq
    rw [Proof.MlKem.Arm.setWidth_append32, hx0]
    simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
    exact hq
  · rw [decide_eq_true (by simpa using h8)] at hc1
    refine wp_ite_t hc1 (wp_movImm (by decide) fun s2 o2 e2 => wp_nil ⟨⟨fun r hr => ?_, by rw [o2.sp, o1.sp]⟩, ?_⟩)
    · have h0 : r ∉ [Reg.r0] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      have h12 : r ∉ [Reg.r12] := fun e => by simp only [List.mem_singleton] at e; subst e; revert hr; decide
      rw [o2.gpr r h0, o1.gpr r h12]
    · sig_post [verifyMessageContract, verifyMessageSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega), Proof.MlKem.Arm.setWidth_append32, e2]

end VG.Proof.MlDsa.Arm.Message
