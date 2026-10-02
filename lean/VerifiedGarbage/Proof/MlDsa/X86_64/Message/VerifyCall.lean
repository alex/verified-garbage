import VerifiedGarbage.Proof.MlDsa.X86_64.Message.VerifyPre
import VerifiedGarbage.Proof.MlDsa.X86_64.Message.Rel
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified

/-!
# ML-DSA on x86-64, `verify_message`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. Any code that meets the
contract the proof of `vg_mldsa*_verify` is written against (`verifyK p`),
never writes `rsp` and whose calls nest at most three deep (`VerifyFn`): its
call from the frame, on `pk`, `μ` at `X + 840`, `sig` and the first
`scratchWords p` words of `scratch` (`verifyCall_ok`).
-/

namespace VG.Proof.MlDsa.X86_64.Message

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlDsa.X86_64.Verify (verifyK)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A verification function on `μ` that `verify_message` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ok : ∀ s, (verifyK p).pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ (verifyK p).post s s'
  ct : ConstantTime isa (verifyK p).pre (verifyK p).pub c
  nosp : NoSp c
  depth : c.depth ≤ 3

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs (p : Params) : List Arg := [.slot fKey, aMu p, .slot fSig, .slot fScr]

theorem verifyArgs_ok {p : Params} (hp : p ∈ params) : (verifyArgs p).all Arg.ok = true := by
  have := oE_lt hp
  simp only [verifyArgs, Impl.MlDsa.X86_64.Message.aMu, List.all_cons, List.all_nil, Arg.ok, fKey, fSig,
    fScr, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The working space of the verification function on `μ`. -/
abbrev rScrV (p : Params) (L : Lay) : Region := ⟨L.scr, Verify.scrLen p⟩

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (L : Lay) : List Region := [⟨L.key, p.pkLen⟩, ⟨L.MU, 64⟩, ⟨L.sig, p.sigLen⟩]
abbrev verifyWr (p : Params) (L : Lay) : List Region := [rScrV p L]

/-- What a layout of `verify_message` says of `sig` and `scratch`. -/
structure VFacts (p : Params) (L : Lay) : Prop where
  key : L.keyLen = p.pkLen
  e : oE p = L.E
  inSig : (⟨L.sig, p.sigLen⟩ : Region) ∈ L.rd
  inScr : ∃ R ∈ L.wr, Within (rScrV p L) R
  inMu : ∃ R ∈ L.wr, Within ⟨L.MU, 64⟩ R
  sigScr : Region.Disjoint ⟨L.sig, p.sigLen⟩ ⟨L.scr, mScrLen p⟩
  keyScr : Region.Disjoint ⟨L.key, p.pkLen⟩ ⟨L.scr, mScrLen p⟩
  kSig : L.STK.Disjoint ⟨L.sig, p.sigLen⟩
  kScr : L.STK.Disjoint ⟨L.scr, mScrLen p⟩
  nSig : L.sig.toNat + p.sigLen ≤ 2 ^ 64
  nScr : L.scr.toNat + mScrLen p ≤ 2 ^ 64

/-- The layout is that of a run of `verify_message` from a state with the
memory `m`, past the branch on `ctx_len`. -/
def VOk (p : Params) (L : Lay) (m : Mem) : Prop :=
  ∃ σ, VPre p σ ∧ (σ.gpr .r8).toNat < 256 ∧ vlay p σ = L ∧ σ.mem = m

theorem scrV_sub (p : Params) (L : Lay) : Region.Sub (rScrV p L) ⟨L.scr, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [Verify.scrLen, oE]; omega)

theorem VOk.facts {p : Params} {L : Lay} {m : Mem} (h : VOk p L m) : VFacts p L := by
  obtain ⟨σ, hσ, _, rfl, -⟩ := h
  exact ⟨rfl, rfl, by simp [vlay, hσ.rd],
    ⟨vScr p σ, by simp [vlay, hσ.wr], within_base _ (by rw [mScr_eq]; simp only [Verify.scrLen, oE]; omega)⟩,
    ⟨vScr p σ, by simp [vlay, hσ.wr],
      (within_off (vlay p σ).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (vlay_X p σ)⟩,
    hσ.sigScr, hσ.pkScr, hσ.stkSig, hσ.stkScr, hσ.nSig, hσ.nScr⟩

/-- The registers after the moves of the arguments of the verification function on `μ`. -/
theorem verifyRegsL {p : Params} {L : Lay} (hE : oE p = L.E) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}
    {t t1 : State} (hc : Ctx L g mx m₀ t) (hm : Moved (verifyArgs p) t t1) :
    t1.gpr .rdi = L.key ∧ t1.gpr .rsi = L.MU ∧ t1.gpr .rdx = L.sig ∧ t1.gpr .rcx = L.scr := by
  obtain ⟨e1, e2, e3, e4⟩ := argsIn4 hm.1.1
  rw [hc.slot, fKey, hc.pKey] at e1
  rw [hc.aMu p hE] at e2
  rw [hc.slot, fSig, hc.pSig] at e3
  rw [hc.slot, fScr, hc.pScr] at e4
  exact ⟨e1, e2, e3, e4⟩

theorem mu_scrV {p : Params} (hp : p ∈ params) {L : Lay} (hE : oE p = L.E) :
    Region.Disjoint ⟨L.MU, 64⟩ (rScrV p L) := by
  show Region.Disjoint ⟨L.scr + BitVec.ofNat 64 L.E + BitVec.ofNat 64 840, 64⟩ ⟨L.scr, Verify.scrLen p⟩
  rw [add_add, ← hE]
  exact Offset.disjoint_base _ (by simp only [Verify.scrLen, oE]; omega) (by have := oE_lt hp; omega)

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_pre {p : Params} (hp : p ∈ params) {L : Lay} (hL : L.Ok) (F : VFacts p L)
    {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t t1 : State} (hc : Ctx L g mx m₀ t)
    (hm : Moved (verifyArgs p) t t1) :
    (verifyK p).pre (t1.callEntry.withRegions (verifyRd p L) (verifyWr p L)) := by
  have hc1 : Ctx L g mx m₀ t1 :=
    hc.regs hm.2.2.1 hm.2.2.2 hm.1.2.1 hm.1.2.2 fun r hr => hm.2.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4⟩ := verifyRegsL F.e hc hm
  have hsub := scrV_sub p L
  have hX : Within L.XS ⟨L.scr, mScrLen p⟩ := ⟨L.E, rfl, by rw [mScr_eq, F.e]⟩
  have hmu : Region.Sub ⟨L.MU, 64⟩ ⟨L.scr, mScrLen p⟩ :=
    ((within_off L.X (d := 840) (n := 64) (k := 1024) (by omega)).trans hX).sub
  have hB := hL.nB
  have hE := oE_lt hp
  have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
  have hrsp : t1.callEntry.gpr .rsp = L.B + BitVec.ofNat 64 24 := by
    rw [State.callEntry_rsp, hc1.rsp, Lay.SP]; exact sp_sub8 _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
    State.callEntry_gpr _ (by decide : Reg.rdi ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rsi ≠ .rsp),
    State.callEntry_gpr _ (by decide : Reg.rdx ≠ .rsp), State.callEntry_gpr _ (by decide : Reg.rcx ≠ .rsp),
    hrsp, e1, e2, e3, e4, below24]
  · rw [toNat_add_ofNat (by omega)]; omega
  · exact F.keyScr.sub_right hsub
  · exact mu_scrV hp F.e
  · exact F.sigScr.sub_right hsub
  · exact hL.stk_r (hkey ▸ hL.kKey) (by omega)
  · exact hL.stk_x (d := 24) (n := 8) (e := 840) (k := 64) (by omega) (by omega)
  · exact hL.stk_r F.kSig (by omega)
  · exact hL.stk_r (F.kScr.sub_right hsub) (by omega)
  · exact (hkey ▸ hL.kKey).sub_left (Region.sub_prefix (by omega))
  · exact (hL.kX.sub_left (Region.sub_prefix (by omega))).sub_right (Offset.sub_base _ (by omega))
  · exact F.kSig.sub_left (Region.sub_prefix (by omega))
  · exact (F.kScr.sub_right hsub).sub_left (Region.sub_prefix (by omega))
  · exact F.key ▸ hL.nKey
  · show L.MU.toNat + 64 ≤ 2 ^ 64
    have hn : L.scr.toNat + (L.E + 1024) ≤ 2 ^ 64 := by rw [← F.e, ← mScr_eq]; exact F.nScr
    show (L.scr + BitVec.ofNat 64 L.E + BitVec.ofNat 64 840).toNat + 64 ≤ 2 ^ 64
    rw [add_add]
    generalize L.E = e at hn ⊢
    generalize L.scr = x at hn ⊢
    clear hc hc1 hm e1 e2 e3 e4 hsub hX hmu hkey hrsp F hL
    have hlt : x.toNat + (e + 840) < x.toNat + (e + 1024) :=
      Nat.add_lt_add_left (Nat.add_lt_add_left (by decide : 840 < 1024) e) _
    rw [toNat_add_ofNat (Nat.lt_of_lt_of_le hlt hn), Nat.add_assoc]
    exact Nat.le_trans (Nat.add_le_add_left (Nat.add_le_add_left (by decide : 840 + 64 ≤ 1024) e) _) hn
  · exact F.nSig
  · have := F.nScr; simp only [mScrLen, Verify.scrLen, messageScratchWords] at this ⊢; omega

/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {p : Params} {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params)
    {L : Lay} (hL : L.Ok) (F : VFacts p L) {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx L g mx m₀ t) :
    WP isa (callA n c (verifyArgs p)) t fun s' =>
      s'.rd = t.rd ∧ s'.wr = t.wr ∧ s'.gpr .rsp = t.gpr .rsp ∧ (∀ r ∈ calleeSaved, s'.gpr r = t.gpr r) ∧
      s'.mxcsr.extractLsb' 6 10 = t.mxcsr.extractLsb' 6 10 ∧
      Frame [rScrV p L, ⟨L.B, 32⟩] t.mem s'.mem ∧
      (let v := fun b => verifyMu p b (bytesAt t.mem L.key p.pkLen) (bytesAt t.mem L.MU 64)
          (bytesAt t.mem L.sig p.sigLen);
        (Verify.res s' = 1 ∧ ∃ b, v b = some true) ∨ (Verify.res s' = 0 ∧ v minBounds ≠ some true)) := by
  refine WP.seq (WP.mono (setArgs_ok _ (verifyArgs_ok hp) t hc.frOk) fun t1 hm => ?_)
  obtain ⟨⟨hA, hm', hx⟩, k⟩ := hm
  have hc1 : Ctx L g mx m₀ t1 := hc.regs k.2.1 k.2.2 hm' hx fun r hr => k.gpr (argRegs_cs r hr)
  obtain ⟨e1, e2, e3, e4⟩ := verifyRegsL F.e hc ⟨⟨hA, hm', hx⟩, k⟩
  have hpre := verifyK_pre hp hL F hc ⟨⟨hA, hm', hx⟩, k⟩
  have hdep := hV.depth
  have hrsp1 : t1.gpr .rsp = L.SP := hc1.rsp
  have hkey : (⟨L.key, p.pkLen⟩ : Region) = L.KEY := by rw [Lay.KEY, F.key]
  refine WP.call_mx hV.ok hV.nosp (by omega) hpre ?_ ?_ fun s' hrd hwr hcs hf _ hpost hmx => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.KEY, List.mem_append_left _ hL.inKey, by rw [hkey]; exact within_self _⟩
    · obtain ⟨R, hR, hw⟩ := F.inMu; exact ⟨R, by simp [hR], hw⟩
    · exact ⟨_, by simp [F.inSig], within_self _⟩
    · obtain ⟨R, hR, hw⟩ := F.inScr; exact ⟨R, by simp [hR], hw⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    obtain ⟨R, hR, hw⟩ := F.inScr; exact ⟨R, List.mem_cons_of_mem _ hR, hw⟩
  obtain ⟨s₂, hm₂, hg₂, hq⟩ := hpost
  refine ⟨hrd.trans k.2.1, hwr.trans k.2.2, by rw [hcs .rsp (by decide), k.gpr (by decide)],
    fun r hr => by rw [hcs r hr, k.gpr (argRegs_cs r hr)], by rw [hmx, hx], ?_, ?_⟩
  · rw [← hm']
    refine Frame.sub hf fun r hr => ?_
    rcases List.mem_append.mp hr with hr | hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨rScrV p L, List.mem_cons_self .., fun _ h => h⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨⟨L.B, 32⟩, List.mem_cons_of_mem _ (List.mem_singleton_self _), ?_⟩
      rw [hrsp1]
      exact below_call_sub _ (by omega)
  · simp only [verifyK, Verify.vPk, Verify.vMu, Verify.vSig, State.withRegions_mem,
      gpr_ce t1 _ _ (by decide : Reg.rdi ≠ .rsp), gpr_ce t1 _ _ (by decide : Reg.rsi ≠ .rsp),
      gpr_ce t1 _ _ (by decide : Reg.rdx ≠ .rsp), e1, e2, e3, Verify.res] at hq
    rw [hc1.ce_bytesAt (p := L.key) (hL.stk_r (hkey ▸ hL.kKey) (by omega)) (by have := hL.nKey; rw [F.key] at this; omega),
      hc1.ce_bytesAt (p := L.MU) (hL.stk_x (d := 24) (n := 8) (e := 840) (k := 64) (by omega) (by omega)) (by omega),
      hc1.ce_bytesAt (p := L.sig) (hL.stk_r F.kSig (by omega)) (by have := F.nSig; omega), hm',
      hg₂ _ (by decide)] at hq
    exact hq

end VG.Proof.MlDsa.X86_64.Message
