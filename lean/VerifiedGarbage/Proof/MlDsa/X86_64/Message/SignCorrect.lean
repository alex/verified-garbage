import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignCall

/-!
# ML-DSA on x86-64, `sign_message`: correctness

Untrusted: everything here is checked by Lean. From a state satisfying
`signMessageContract p X86_64.abi 104`, `signMessage n c p` returns 2 if
the context string is longer than 255 bytes; otherwise it computes `μ` of
the formatted message and calls the signing function on `μ` `c`, which
gives the signature of `ML-DSA.Sign_internal` on the formatted message
(`signMessage_correct`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86_64 (Keep WP.keep)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-! ## The branch on `ctx_len` -/

theorem wp_ite_t {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some true) (h : WP isa th s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteT hc e, q⟩

theorem wp_ite_f {c : isa.Cond} {th el : Prog isa} {s : State} {Q : State → Prop}
    (hc : isa.eval c s = some false) (h : WP isa el s Q) : WP isa (.ite c th el) s Q :=
  let ⟨_, _, e, q⟩ := h; ⟨_, _, .iteF hc e, q⟩

/-- `cmp r8, 256`. -/
theorem cmp_ok (s : State) :
    WP isa (.block [.alu .cmp .r8 (.imm 256)]) s fun s1 => s1.gpr = s.gpr ∧ s1.mem = s.mem ∧
      s1.rd = s.rd ∧ s1.wr = s.wr ∧ s1.mxcsr = s.mxcsr ∧
      isa.eval .b s1 = some (decide ((s.gpr .r8).toNat < 256)) := by
  xrun [show BitVec.signExtend 64 (256 : BitVec 32) = 256 by decide]
  exact ⟨rfl, rfl⟩

/-! ## Before the frame -/

theorem stackArgAddr0 (s : State) : stackArgAddr s 0 = s.gpr .rsp + BitVec.ofNat 64 8 := rfl

/-- `sig` to `r10`, `scratch` to `r11`, 0 to `rax`. -/
theorem signMov_ok {p : Params} {s s1 : State} (h : SPre p s) (hg : s1.gpr = s.gpr) (hm : s1.mem = s.mem)
    (hrd : s1.rd = s.rd) :
    WP isa (.block [.mov .r10 (.mem (stk 8)), .mov .r11 (.mem (stk 16)), .mov32 .rax (.imm 0)]) s1 fun s2 =>
      (s2.gpr .r10 = stackArg s 0 ∧ s2.gpr .r11 = stackArg s 1 ∧ s2.gpr .rax = 0 ∧ s2.mem = s.mem ∧
        s2.mxcsr = s1.mxcsr) ∧ Keep [.r10, .r11, .rax] s1 s2 := by
  have hin : ∀ d, d + 8 ≤ 16 → InRegions (s1.rd ++ s1.wr) (s1.gpr .rsp + BitVec.ofNat 64 (8 + d)) 8 := by
    intro d hd
    refine ⟨rArgs s, by simp [hrd, h.rd], ?_⟩
    rw [hg, ← add_add, ← stackArgAddr0]
    exact Offset.contains_base _ hd (by omega)
  refine WP.keep _ ?_ (by decide)
  have h8 := hin 0 (by omega)
  have h16 := hin 8 (by omega)
  simp only [Nat.add_zero, Nat.reduceAdd] at h8 h16
  xrun [ea_stk, h8, h16, RegUpd.mxcsr_setReg]
  rw [hm, hg]
  exact ⟨rfl, rfl, rfl⟩

/-! ## The function -/

theorem cs_r11 : ∀ r ∈ calleeSaved, r ≠ .r11 := by decide
theorem cs_tmp : ∀ r ∈ calleeSaved, r ∉ [Reg.r10, .r11, .rax] := by decide

/-- The arguments of `signRegs`, pushed. -/
theorem signRegs_vals {p : Params} {s s2 : State} (hk : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r)
    (h10 : s2.gpr .r10 = stackArg s 0) (h11 : s2.gpr .r11 = stackArg s 1) (hax : s2.gpr .rax = 0) :
    ∀ j (hj : j < 9), s2.gpr (signRegs[j]'(by simp [signRegs]; omega)) =
      (slay p s).vals[j]'(by simp [Lay.vals]; omega) := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [signRegs, Lay.vals, slay, List.getElem_cons_zero, List.getElem_cons_succ, h10, h11, hax] <;>
    exact hk _ (by decide)

theorem signMessage_wp {p : Params} {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params)
    {s : State} (hpre : (signMessageContract p X86_64.abi 104).pre s) :
    WP isa (signMessage n c p) s fun s' =>
      abiPreserved s s' ∧ (signMessageContract p X86_64.abi 104).post s s' := by
  have h := sPre_of hpre
  unfold signMessage top
  refine WP.seq (WP.mono (cmp_ok s) fun s1 ⟨hg1, hm1, hrd1, hwr1, hx1, hc1⟩ => ?_)
  by_cases h8 : (s.gpr .r8).toNat < 256
  · rw [decide_eq_true h8] at hc1
    refine wp_ite_t hc1 (WP.seq (WP.mono (signMov_ok h hg1 hm1 hrd1) fun s2 ⟨⟨h10, h11, hax, hm2, hx2⟩, k2⟩ => ?_))
    have hL := slay_ok hp h h8
    have hg2 : ∀ r, r ∉ [Reg.r10, .r11, .rax] → s2.gpr r = s.gpr r := fun r hr => (k2.gpr hr).trans (by rw [hg1])
    have hsp2 : s2.gpr .rsp = (slay p s).B + BitVec.ofNat 64 104 := by
      rw [hg2 _ (by decide), slay_B]
    have hn : 8 * signRegs.length ≤ (s2.gpr .rsp).toNat := by
      rw [hg2 _ (by decide)]; have := h.sp; simp only [signRegs, List.length_cons, List.length_nil]; omega
    refine WP.frame (by decide) (by decide) (by decide) hn ?_
    refine WP.seq (WP.mono (entry_ok hL rfl (by decide) hsp2 (k2.2.1.trans hrd1) (k2.2.2.trans hwr1)
      (signRegs_vals hg2 h10 h11 hax) (hg2 _ (by decide)))
      fun t ⟨hc, htw, htsp⟩ => ?_)
    have hsk := skLen_ge hp
    have wtr : Within ⟨(slay p s).key + BitVec.ofNat 64 64, 64⟩ (slay p s).KEY :=
      within_off _ (show 64 + 64 ≤ p.skLen by omega)
    refine WP.seq (WP.mono (muHash_ok hL rfl hc (tr := .slotOff fKey 64) (by decide)
      (fun t' hc' => by rw [hc'.slotOff, fKey, hc'.pKey]) ⟨_, List.mem_append_left _ hL.inKey, wtr⟩
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Region.sub_prefix (by decide : 200 ≤ 1024)))
      ((hL.xKey.symm.sub_left wtr.sub).sub_right (Offset.sub_base _ (by decide : 200 + 640 ≤ 1024)))
      ((hL.kKey.sub_left (Region.sub_prefix (by decide : 32 ≤ 104))).sub_right wtr.sub))
      fun t₁ ⟨hc₁, hf₁, hμ⟩ => ?_)
    refine WP.mono (signCall_ok hS hp h h8 hc₁) fun s' ⟨hrd', hwr', hsp', hcs', hx', hf', hq⟩ => ?_
    have hm₀ : s2.mem = s.mem := hm2
    refine ⟨by rw [hsp', hc₁.rsp, ← htsp, hc.rsp], by rw [hwr', hc₁.wr, ← htw, hc.wr], ?_, ?_⟩
    · -- The calling convention.
      refine ⟨fun r hr => ?_, ?_, ?_⟩
      · by_cases hr' : r = .rsp
        · subst hr'
          rw [popped_rsp, hsp', hc₁.rsp, Lay.SP, add_add, show 32 + 8 * signRegs.length = 104 from rfl, slay_B]
        · rw [popped_gpr _ _ _ hr' (cs_r11 r hr), hcs' r hr, hc₁.cs r hr hr', hg2 r (cs_tmp r hr)]
      · have eR : rRet s = ⟨(slay p s).B + BitVec.ofNat 64 104, 8⟩ := by rw [slay_B]
        have dB : ∀ k, k ≤ 104 → (rRet s).Disjoint ⟨(slay p s).B, k⟩ := fun k hk => by
          rw [eR]; exact Offset.disjoint_base _ hk (by have := hL.nB; omega)
        rw [popped_mem, hf'.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | rfl
            · exact h.retSig
            · exact h.retScr.sub_right (scrMu_sub p s)
            · exact dB 32 (by decide)) (by decide),
          hc₁.frame.readW (r := rRet s) (Region.contains_self _ _) (fun r hr => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl
            · exact h.retScr.sub_right (slay_X p s).sub
            · exact dB 104 (by decide)) (by decide), hm₀]
      · rw [popped_mxcsr, hx', hc₁.mx, hx2, hx1]
    · sig_post [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
      rw [formatMessage_some (by rw [Proof.MlKem.bytesAt_length]; exact h8)]
      simp only [signInternal, messageRep, skTr]
      have ek : bytesAt t₁.mem (s.gpr .rdi) p.skLen = bytesAt s.mem (s.gpr .rdi) p.skLen := by
        rw [hc₁.bytesAt_eq (p := s.gpr .rdi) (n := p.skLen) hL.xKey hL.kKey (by have := h.nSk; omega), hm₀]
      have er : bytesAt t₁.mem (s.gpr .r9) 32 = bytesAt s.mem (s.gpr .r9) 32 := by
        rw [hc₁.bytesAt_eq (p := s.gpr .r9) (n := 32) (h.rndScr.symm.sub_left (slay_X p s).sub) h.stkRnd (by decide), hm₀]
      have etr : bytesAt t.mem ((slay p s).key + BitVec.ofNat 64 64) 64 =
          ((bytesAt s.mem (s.gpr .rdi) p.skLen).drop 64).take 64 := by
        rw [hc.bytesAt_eq (hL.xKey.sub_right wtr.sub) (hL.kKey.sub_right wtr.sub) (by decide), hm₀,
          Proof.MlKem.bytesAt_slice _ _ (by omega)]
        rfl
      rw [ek, er, hμ, etr, hm₀] at hq
      simp only [hdrBytes, Proof.MlKem.bytesAt_length, List.append_assoc] at hq ⊢
      exact hq
  · rw [decide_eq_false h8] at hc1
    refine wp_ite_f hc1 ?_
    xrun [show (2 : BitVec 32) = BitVec.ofNat 32 2 from rfl]
    refine ⟨⟨fun r hr => ?_, by rw [RegUpd.mem_setReg, hm1], by rw [RegUpd.mxcsr_setReg, hx1]⟩, ?_⟩
    · rw [RegUpd.gpr_setReg_of_ne _ _ (fun e => by subst e; revert hr; decide), hg1]
    · sig_post [signMessageContract, signMessageSig, X86_64.abi, X86_64.argRegs, List.range, List.range.loop]
      rw [formatMessage_none (by rw [Proof.MlKem.bytesAt_length]; omega)]
      rfl

end VG.Proof.MlDsa.X86_64.Message
