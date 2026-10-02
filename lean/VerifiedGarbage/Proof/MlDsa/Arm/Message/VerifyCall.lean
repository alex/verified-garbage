import VerifiedGarbage.Proof.MlDsa.Arm.Message.SignCall

/-!
# ML-DSA on ARMv7, `verify_message`: the call of the verification function on `μ`

Untrusted: everything here is checked by Lean. Any code verified against
`verifyContract p Arm.abi 36` whose frames use at most 36 bytes of stack
(`VerifyFn`): its call on the key, `μ` at `X + 840`, `sig` and the first
`scratchWords p` words of `scratch` (`verifyCall_ok`), after which the saves
are intact (`Fin`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A verification function on `μ` that `verify_message` can call. -/
structure VerifyFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified Arm.target c (verifyContract p Arm.abi 36)
  su : stackUse c ≤ 36

/-- The precondition of `verifyContract p Arm.abi 36`, from its facts. -/
theorem verifyC_pre {p : Params} {E : State} (sp : 36 ≤ E.sp.toNat)
    (rd : E.rd = [⟨State.addr (E.gpr .r0), p.pkLen⟩, ⟨State.addr (E.gpr .r1), 64⟩,
      ⟨State.addr (E.gpr .r2), p.sigLen⟩])
    (wr : E.wr = [⟨State.addr (E.gpr .r3), sScr p⟩])
    (d03 : Region.Disjoint ⟨State.addr (E.gpr .r0), p.pkLen⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (d13 : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (d23 : Region.Disjoint ⟨State.addr (E.gpr .r2), p.sigLen⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (k0 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r0), p.pkLen⟩)
    (k1 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r1), 64⟩)
    (k2 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r2), p.sigLen⟩)
    (k3 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 36, 36⟩ ⟨State.addr (E.gpr .r3), sScr p⟩)
    (n0 : (E.gpr .r0).toNat + p.pkLen ≤ 2 ^ 32) (n1 : (E.gpr .r1).toNat + 64 ≤ 2 ^ 32)
    (n2 : (E.gpr .r2).toNat + p.sigLen ≤ 2 ^ 32) (n3 : (E.gpr .r3).toNat + sScr p ≤ 2 ^ 32) :
    (verifyContract p Arm.abi 36).pre E := by
  sig_pre [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨sp, by have := E.sp.isLt; omega, rd, wr, d03, d13, d23, k0, k1, k2, k3, n0, n1, n2, n3⟩

/-- The arguments of the call of the verification function on `μ`. -/
abbrev verifyArgs : List (Reg × Arg) := [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fSig), (.r3, .slot fScr)]

section
variable {p : Params} {s : State}

/-- The regions the verification function on `μ` reads and writes. -/
abbrev verifyRd (p : Params) (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), p.pkLen⟩, ⟨(vlay p s).MU, 64⟩, ⟨State.addr (stackArg s 1), p.sigLen⟩]
abbrev verifyWr (p : Params) (s : State) : List Region := [⟨State.addr (stackArg s 2), sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem verifyRegs_of (hL : (vlay p s).Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (vlay p s) g m₀ t) (hm : (∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .r0 = s.gpr .r0 ∧ t1.gpr .r1 = (vlay p s).X32 + BitVec.ofNat 32 840 ∧ t1.gpr .r2 = stackArg s 1 ∧
      t1.gpr .r3 = stackArg s 2 := by
  have e0 := hm (.r0, .slot fKey) (by simp)
  have e1 := hm (.r1, .off oMU) (by simp)
  have e2 := hm (.r2, .slot fSig) (by simp)
  have e3 := hm (.r3, .slot fScr) (by simp)
  rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV hL (f := fSig) (j := 6) rfl (by omega)] at e2
  rw [hc.slotV hL (f := fScr) (j := 7) rfl (by omega)] at e3
  simp only [Lay.vals, vlay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3
  exact ⟨e0, e1, e2, e3⟩

/-- The precondition of the verification function on `μ`, on entry to it. -/
theorem verifyK_pre (hp : p ∈ params) (h : VPre p s) (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 : State} (hc : Ctx (vlay p s) g m₀ t)
    (hA : ∀ da ∈ verifyArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (verifyContract p Arm.abi 36).pre (t1.callEntry.withRegions (verifyRd p s) (verifyWr p s)) := by
  have hL := vlay_ok hp h h8
  obtain ⟨e0, e1, e2, e3⟩ := verifyRegs_of hL hc hA
  have hsub := sScr_sub p (State.addr (stackArg s 2))
  generalize hE : t1.callEntry.withRegions (verifyRd p s) (verifyWr p s) = E
  have gr : ∀ {r : Reg}, r ∉ linkRegs → E.gpr r = t1.gpr r := fun hr => by
    rw [← hE, State.withRegions_gpr, State.callEntry_gpr _ hr]
  have g0 : E.gpr .r0 = s.gpr .r0 := by rw [gr (by decide), e0]
  have g1 : State.addr (E.gpr .r1) = (vlay p s).MU := by rw [gr (by decide), e1, mu_eq hL]
  have g2 : E.gpr .r2 = stackArg s 1 := by rw [gr (by decide), e2]
  have g3 : E.gpr .r3 = stackArg s 2 := by rw [gr (by decide), e3]
  have gsp : E.sp = s.sp := by rw [← hE, State.withRegions_sp, State.callEntry_sp, hsp1]
  have grd : E.rd = verifyRd p s := by rw [← hE]; rfl
  have gwr : E.wr = verifyWr p s := by rw [← hE]; rfl
  refine verifyC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> try simp only [g0, g1, g2, g3, gsp, grd, gwr]
  · exact h.sp
  · exact h.pkScr.sub_right hsub
  · exact x_sScr hL rfl (by omega)
  · exact h.sigScr.sub_right hsub
  · exact h.stkPk
  · have km := k_mu hL
    simp only [Lay.STK] at km
    rw [show (vlay p s).SP = s.sp from rfl] at km
    exact km
  · exact h.stkSig
  · exact h.stkScr.sub_right hsub
  · exact h.nPk
  · rw [gr (by decide), e1]
    have := hL.x32_lt
    rw [x32_toNat hL (by omega)]; omega
  · exact h.nSig
  · have := h.nScr; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega

/-- The call of the verification function on `μ`. -/
theorem verifyCall_ok {n : String} {c : Prog isa} (hV : VerifyFn p c) (hp : p ∈ params) (h : VPre p s)
    (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx (vlay p s) g m₀ t) :
    WP isa (.seq (.block (setArgs verifyArgs)) (.call n c)) t fun s' => Fin (vlay p s) g s' ∧
      (let w := fun b => verifyMu p b (bytesAt t.mem (State.addr (s.gpr .r0)) p.pkLen)
          (bytesAt t.mem (vlay p s).MU 64) (bytesAt t.mem (State.addr (stackArg s 1)) p.sigLen);
        (s'.gpr .r0 = 1 ∧ ∃ b, w b = some true) ∨ (s'.gpr .r0 = 0 ∧ w minBounds ≠ some true)) := by
  have hL := vlay_ok hp h h8
  refine WP.seq (WP.mono (setArgs_ok verifyArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx (vlay p s) g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl =>
    o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  obtain ⟨e0, e1, e2, _⟩ := verifyRegs_of hL hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hpre := verifyK_pre hp h h8 hc hA hsp1
  refine WP.callF hV.ver.1 hpre ?_ ?_ (by rw [hsp1]; have := hV.su; have := h.sp; omega)
    fun s' hrd hwr hsp hf hcs hpost => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [vlay, h.rd], within_self _⟩
    · exact ⟨_, by simp [vlay, h.wr], mu_within hL⟩
    · exact ⟨_, by simp [vlay, h.rd], within_self _⟩
    · exact ⟨⟨State.addr (stackArg s 2), mScrLen p⟩, by simp [vlay, h.wr],
        within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact ⟨⟨State.addr (stackArg s 2), mScrLen p⟩, by simp [vlay, h.wr],
      within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 4 ≤ 120 → s'.mem.readW ((vlay p s).X + BitVec.ofNat 64 (904 + d)) 32 =
      t1.mem.readW ((vlay p s).X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact x_sScr hL rfl (by omega)
      · rw [hsp1]
        exact hL.sv_disj (r := belowA s.sp (stackUse c)) (.inr (belowA_sub hV.su)) hd') (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .r7 (by decide) (by decide)).trans hc1.r7,
    fun r hr h7 hl => (hcs r hr hl).trans (hc1.cs r hr h7 hl),
    (hsv 0 (by omega)).trans hc1.s7, (hsv 4 (by omega)).trans hc1.sLR⟩, ?_⟩
  sig_reduce [verifyContract, verifySig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
  rw [e0, e1, e2, Proof.MlKem.Arm.setWidth_append32, o.mem] at hpost
  rw [show BitVec.setWidth 64 ((vlay p s).X32 + 840#32) = (vlay p s).MU from mu_eq hL] at hpost
  exact hpost

end

end VG.Proof.MlDsa.Arm.Message
