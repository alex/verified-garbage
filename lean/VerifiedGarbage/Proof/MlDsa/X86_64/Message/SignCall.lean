import VerifiedGarbage.Proof.MlDsa.X86_64.Message.SignPre
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Verified

/-!
# ML-DSA on x86-64, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. Any code that meets the
contract the proof of `vg_mldsa*_sign` is written against (`signK p 24`),
never writes `rsp` and whose calls nest at most three deep (`SignFn`): its
call from the frame, on the key, `μ` at `X + 840`, `rnd`, `sig` and the
first `scratchWords p` words of `scratch` (`signCall_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlKem.X86_64 (Keep)
open VG.Proof.MlDsa.X86_64.Sign (signK scrLen)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (signK p 24).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (signK p 24).post s s'
  ct : ConstantTime isa (signK p 24).pre (signK p 24).pub c
  nosp : NoSp c
  depth : c.depth ≤ 3

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs (p : Params) : List Arg := [.slot fKey, aMu p, .slot fRnd, .slot fSig, .slot fScr]

section
variable {p : Params} {s : State}

/-- The working space of the signing function on `μ`. -/
abbrev rScrMu (p : Params) (s : State) : Region := ⟨stackArg s 1, scrLen p⟩

theorem scrMu_sub (p : Params) (s : State) : Region.Sub (rScrMu p s) (rScr p s) :=
  Region.sub_prefix (by rw [mScr_eq]; simp [scrLen, oE])

theorem mu_within (p : Params) (s : State) : Within ⟨(slay p s).MU, 64⟩ (rScr p s) :=
  (within_off (slay p s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (slay_X p s)

theorem mu_scrMu {p : Params} (hp : p ∈ params) (s : State) : Region.Disjoint ⟨(slay p s).MU, 64⟩ (rScrMu p s) := by
  show Region.Disjoint ⟨stackArg s 1 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ ⟨stackArg s 1, scrLen p⟩
  rw [add_add]
  exact Offset.disjoint_base _ (by simp [scrLen, oE]) (by have := oE_lt hp; omega)

theorem below24 (B : Addr) : below (B + BitVec.ofNat 64 24) 24 = ⟨B, 24⟩ := by
  show (⟨B + BitVec.ofNat 64 24 - BitVec.ofNat 64 24, 24⟩ : Region) = _
  rw [BitVec.add_sub_cancel]

/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) (h : SPre p s)
    (h8 : (s.gpr .r8).toNat < 256) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx (slay p s) g mx m₀ t) :
    WP isa (callA n c (signArgs p)) t fun s' =>
      s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .rsp = t.gpr .rsp ∧ (∀ r ∈ calleeSaved, s'.gpr r = t.gpr r) ∧
      s'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame [rSig p s, rScrMu p s, ⟨(slay p s).B, 32⟩] t.mem s'.mem ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (s.gpr .rdi) p.skLen) (bytesAt t.mem (slay p s).MU 64)
          (bytesAt t.mem (s.gpr .r9) 32)) ((s'.gpr .rax).setWidth 32)
        (bytesAt s'.mem (stackArg s 0) p.sigLen) := by
  have hL := slay_ok hp h h8
  have hok : (signArgs p).all Arg.ok = true := by
    have := hL.hE
    simp only [signArgs, Impl.MlDsa.X86_64.Message.aMu, List.all_cons, List.all_nil, Arg.ok, fKey, fRnd, fSig,
      fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    simp only [slay] at this
    omega
  refine WP.seq (WP.mono (setArgs_ok _ hok t hc.frOk) fun t1 ⟨⟨hA, hm, hx⟩, k⟩ => ?_)
  have hc1 : Ctx (slay p s) g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4, e5⟩ := argsIn5 hA
  rw [hc.slot, fKey, hc.pKey] at e1
  rw [hc.aMu p rfl] at e2
  rw [hc.slot, fRnd, hc.pRnd] at e3
  rw [hc.slot, fSig, hc.pSig] at e4
  rw [hc.slot, fScr, hc.pScr] at e5
  have hpre : (signK p 24).pre (t1.callEntry.withRegions
      [⟨s.gpr .rdi, p.skLen⟩, ⟨(slay p s).MU, 64⟩, ⟨s.gpr .r9, 32⟩] [⟨stackArg s 0, p.sigLen⟩, rScrMu p s]) := by
    simp only [signK, State.withRegions_rd, State.withRegions_wr, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.r8 ≠ .rsp), rsp_ce,
      e1, e2, e3, e4, e5, Sign.retR, hc1.rsp, sp_sub8, below24]
    have hsub := scrMu_sub p s
    have hmu := (mu_within p s).sub
    have hB := hL.nB
    have hn := h.nScr
    have hE := oE_lt hp
    refine ⟨rfl, rfl, h.skSig, h.skScr.sub_right hsub, h.sigScr.symm.sub_left hmu, mu_scrMu hp s, h.rndSig,
      h.rndScr.sub_right hsub, h.sigScr.sub_right hsub, hL.stk_r h.stkSk (by omega),
      hL.stk_x (d := 24) (n := 8) (e := 840) (k := 64) (by omega) (by omega), hL.stk_r h.stkRnd (by omega),
      hL.stk_r h.stkSig (by omega), hL.stk_r (h.stkScr.sub_right hsub) (by omega), ?_, ?_, ?_, ?_, ?_, h.nSk, ?_,
      h.nRnd, h.nSig, by simp only [slay, mScrLen, scrLen, messageScratchWords] at hn ⊢; omega, ?_⟩
    · exact h.stkSk.sub_left (Region.sub_prefix (by omega))
    · exact (hL.kX.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))
    · exact h.stkRnd.sub_left (Region.sub_prefix (by omega))
    · exact h.stkSig.sub_left (Region.sub_prefix (by omega))
    · exact (h.stkScr.sub_right hsub).sub_left (Region.sub_prefix (by omega))
    · exact mu_nowrap h
    · rw [toNat_add_ofNat (by omega)]; omega
  have hdep := hS.depth
  have hsub := scrMu_sub p s
  have hrsp1 : t1.gpr .rsp = (slay p s).SP := hc1.rsp
  refine WP.call_mx hS.ok hS.nosp (by omega) hpre ?_ ?_ fun s' hrd hwr hcs hf _ hpost hmx => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨rSk p s, by simp [slay, h.rd], within_self _⟩
    · exact ⟨rScr p s, by simp [slay, h.wr], mu_within p s⟩
    · exact ⟨rRnd s, by simp [slay, h.rd], within_self _⟩
    · exact ⟨rSig p s, by simp [slay, h.wr], within_self _⟩
    · exact ⟨rScr p s, by simp [slay, h.wr], within_base _ (by rw [mScr_eq]; simp [scrLen, oE])⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨rSig p s, by simp [slay, h.wr], within_self _⟩
    · exact ⟨rScr p s, by simp [slay, h.wr], within_base _ (by rw [mScr_eq]; simp [scrLen, oE])⟩
  obtain ⟨s₂, hm₂, hg₂, hq⟩ := hpost
  refine ⟨hrd.trans k.2.1, hwr.trans k.2.2, by rw [hcs .rsp (by decide), k.gpr (by decide)],
    fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], by rw [hmx, hx], ?_, ?_⟩
  · rw [← hm]
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨rSig p s, List.mem_cons_self .., fun _ h => h⟩
      · exact ⟨rScrMu p s, List.mem_cons_of_mem _ (List.mem_cons_self ..), fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨(slay p s).B, 32⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), ?_⟩
      rw [hrsp1]
      exact below_call_sub _ (by omega)
  · simp only [signK, State.withRegions_mem, gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rcx ≠ .rsp), e1, e2, e3, e4, hm₂] at hq
    have hL := slay_ok hp h h8
    rw [hc1.ce_bytesAt (p := (slay p s).key) (hL.stk_r h.stkSk (by omega)) (by have := h.nSk; omega),
      hc1.ce_bytesAt (p := (slay p s).MU) (hL.stk_x (d := 24) (n := 8) (e := 840) (k := 64) (by omega)
        (by omega)) (by omega),
      hc1.ce_bytesAt (p := (slay p s).rnd) (hL.stk_r h.stkRnd (by omega)) (by omega), hm,
      hg₂ _ (by decide)] at hq
    exact hq
