import VerifiedGarbage.Proof.MlDsa.Arm.Message.Pre
import VerifiedGarbage.Proof.MlKem.Arm.CallF

/-!
# ML-DSA on ARMv7, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. A call of verified code with
frames of its own, in a frame that pushes its fifth argument (`r12`) and
`lr` (`frameCall_ok`, as `callS_ok` of the signing function on `μ`, after
the moves of the arguments). Any code verified against `signContract p
Arm.abi 28` whose frames use at most 28 bytes of stack (`SignFn`): its call
on the key, `μ` at `X + 840`, `rnd`, `sig` and the first `scratchWords p`
words of `scratch` (`signCall_ok`), after which the saves are intact
(`Fin`).
-/

namespace VG.Proof.MlDsa.Arm.Message

open VG VG.Arm VG.Impl.MlDsa.Arm.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.Arm (push2_frame push2_arg addr_sub view_gpr below)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified Arm.target c (signContract p Arm.abi 28)
  su : stackUse c ≤ 28

/-- The size of the working space of the functions on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The argument on the stack of a call in a frame: the word at the stack
pointer of the callee. -/
abbrev argR (s : State) : Region := ⟨State.addr s.sp - BitVec.ofNat 64 8, 4⟩

theorem frame8 {s : State} (hsp : 8 ≤ s.sp.toNat) :
    (⟨State.addr (s.sp - BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length)), 4 * [Reg.r12, Reg.lr].length⟩ : Region) =
      belowA s.sp 8 := by
  simp only [belowA, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul]
  rw [addr_sub hsp]

theorem ne12_pres : ∀ r ∈ preserved, r ≠ .lr → r ≠ .r12 := by decide

theorem sp_sub8 {sp : BitVec 32} (h : 8 ≤ sp.toNat) : (sp - BitVec.ofNat 32 8).toNat = sp.toNat - 8 := by
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- A call of verified code in a frame that pushes `r12` (its fifth
argument) and `lr`, from the state after the moves of its arguments. -/
theorem frameCall_ok {D : Nat} {n : String} {c : Prog isa} {k : Contract isa}
    (hv : ∀ s, k.pre s → ∃ t s', Exec isa c s t s' ∧ abiPreserved s s' ∧ k.post s s')
    (hsu : 8 + stackUse c ≤ D) {s : State} (hsp : D ≤ s.sp.toNat) {rd wr : List Region}
    (hpre : k.pre ((pushed [.r12, .lr] s).callEntry.withRegions (rd ++ [argR s]) wr))
    (hc : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    WP isa (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8)) s fun s' =>
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) ∧
      Frame (wr ++ [belowA s.sp D]) s.mem s'.mem ∧
      ∃ s₂ : State, s₂.mem = s'.mem ∧ (∀ r, r ≠ .r12 → s₂.gpr r = s'.gpr r) ∧
        k.post ((pushed [.r12, .lr] s).callEntry.withRegions (rd ++ [argR s]) wr)
          (s₂.withRegions (rd ++ [argR s]) wr) := by
  have h8 : 8 ≤ s.sp.toNat := by omega
  refine WP.frame (rs := [.r12, .lr]) (r := .r12) rfl (by simpa using h8) (by decide) ?_
  have hwp : (pushed [.r12, .lr] s).wr = belowA s.sp 8 :: s.wr := by rw [VG.Arm.pushed_wr, frame8 h8]
  refine WP.callF hv hpre (fun x m hx => ?_) (fun x m hx => ?_) ?_ fun s₂ hrd hwr hsp₂ hf hcs hpost => ?_
  · rw [VG.Arm.pushed_rd, hwp]
    rcases (by simpa only [InRegions, List.mem_append, or_assoc] using hx : ∃ r, (r ∈ rd ∨ r ∈ [argR s] ∨ r ∈ wr) ∧
      r.Contains x m) with ⟨r, (hr | hr | hr), hcr⟩
    · obtain ⟨r', hr', hc'⟩ := hc x m ⟨r, hr, hcr⟩
      rcases List.mem_append.mp hr' with h | h
      · exact ⟨r', List.mem_append_left _ h, hc'⟩
      · exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ h), hc'⟩
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_cons_self ..), ?_⟩
      simp only [Region.Contains, belowA] at hcr ⊢; omega
    · obtain ⟨r', hr', hc'⟩ := hw x m ⟨r, hr, hcr⟩
      exact ⟨r', List.mem_append_right _ (List.mem_cons_of_mem _ hr'), hc'⟩
  · rw [hwp]
    obtain ⟨r', hr', hc'⟩ := hw x m hx
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩
  · rw [VG.Arm.pushed_sp, show BitVec.ofNat 32 (4 * [Reg.r12, Reg.lr].length) = BitVec.ofNat 32 8 from rfl,
      sp_sub8 h8]; omega
  · have hsp₂' : s₂.sp = s.sp - BitVec.ofNat 32 8 := by rw [hsp₂, VG.Arm.pushed_sp]; rfl
    have f₁ := push2_frame h8
    have hsu' : 8 + stackUse c ≤ s.sp.toNat := by omega
    refine ⟨by simp only [popped_rd, hrd, VG.Arm.pushed_rd], by simp only [popped_wr, hwr, hwp, List.tail_cons],
      by rw [popped_sp, hsp₂']; exact BitVec.sub_add_cancel _ _,
      fun r hr hl => by rw [popped_gpr (ne12_pres r hr hl), hcs r hr hl, VG.Arm.pushed_gpr], ?_,
      s₂, rfl, fun r hr => (popped_gpr hr _ _).symm, hpost⟩
    rw [popped_mem]
    rw [VG.Arm.pushed_sp] at hf
    refine (f₁.sub fun r hr => ?_).trans (hf.sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      exact belowA_sub (show 8 ≤ D by omega)
    · simp only [List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact ⟨r, List.mem_append_left _ hr, fun _ h => h⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
          fun x h => belowA_sub (show 8 + stackUse c ≤ D by omega) x (belowA_push hsu' x h)⟩

/-- The precondition of `signContract p Arm.abi 28`, from its facts. -/
theorem signC_pre {p : Params} {E : State} (sp : 28 ≤ E.sp.toNat) (sp4 : E.sp.toNat + 4 ≤ 2 ^ 32)
    (rd : E.rd = [⟨State.addr (E.gpr .r0), p.skLen⟩, ⟨State.addr (E.gpr .r1), 64⟩, ⟨State.addr (E.gpr .r2), 32⟩,
      ⟨stackArgAddr E 0, 4⟩])
    (wr : E.wr = [⟨State.addr (E.gpr .r3), p.sigLen⟩, ⟨State.addr (stackArg E 0), sScr p⟩])
    (d03 : Region.Disjoint ⟨State.addr (E.gpr .r0), p.skLen⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d0s : Region.Disjoint ⟨State.addr (E.gpr .r0), p.skLen⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d13 : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d1s : Region.Disjoint ⟨State.addr (E.gpr .r1), 64⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d23 : Region.Disjoint ⟨State.addr (E.gpr .r2), 32⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (d2s : Region.Disjoint ⟨State.addr (E.gpr .r2), 32⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d3s : Region.Disjoint ⟨State.addr (E.gpr .r3), p.sigLen⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (d3a : Region.Disjoint ⟨State.addr (E.gpr .r3), p.sigLen⟩ ⟨stackArgAddr E 0, 4⟩)
    (dsa : Region.Disjoint ⟨State.addr (stackArg E 0), sScr p⟩ ⟨stackArgAddr E 0, 4⟩)
    (k0 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r0), p.skLen⟩)
    (k1 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r1), 64⟩)
    (k2 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r2), 32⟩)
    (k3 : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (E.gpr .r3), p.sigLen⟩)
    (ks : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨State.addr (stackArg E 0), sScr p⟩)
    (ka : Region.Disjoint ⟨State.addr E.sp - BitVec.ofNat 64 28, 28⟩ ⟨stackArgAddr E 0, 4⟩)
    (n0 : (E.gpr .r0).toNat + p.skLen ≤ 2 ^ 32) (n1 : (E.gpr .r1).toNat + 64 ≤ 2 ^ 32)
    (n2 : (E.gpr .r2).toNat + 32 ≤ 2 ^ 32) (n3 : (E.gpr .r3).toNat + p.sigLen ≤ 2 ^ 32)
    (ns : (stackArg E 0).toNat + sScr p ≤ 2 ^ 32) :
    (signContract p Arm.abi 28).pre E := by
  sig_pre [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val]
  exact ⟨sp, sp4, rd, wr, d03, d0s, d13, d1s, d23, d2s, d3s, d3a, dsa, k0, k1, k2, k3, ks, ka, n0, n1, n2, n3, ns⟩

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × Arg) := [(.r0, .slot fKey), (.r1, .off oMU), (.r2, .slot fRnd), (.r3, .slot fSig),
  (.r12, .slot fScr)]

section
variable {p : Params} {s : State}

/-- The working space of the functions on `μ`: the start of `scratch`. -/
theorem sScr_sub (p : Params) (b : Addr) : Region.Sub ⟨b, sScr p⟩ ⟨b, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [sScr, oE]; omega)

/-- What lies in the 1 KiB is apart from it. -/
theorem x_sScr {L : Lay} (hL : L.Ok) (hE : L.E = oE p) {d n : Nat} (hd : d + n ≤ 1024) :
    Region.Disjoint ⟨L.X + BitVec.ofNat 64 d, n⟩ ⟨State.addr L.scr, sScr p⟩ := by
  rw [hL.x_eq, add_add, hE]
  have := hL.hE; have := hL.nScr
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega) (by omega)

theorem mu_within {L : Lay} (hL : L.Ok) : Within ⟨L.MU, 64⟩ L.SC :=
  (within_off L.X (d := 840) (n := 64) (k := 1024) (by omega)).trans hL.xs_sc

/-- The stack below the callee's stack pointer, in `STK`. -/
theorem stkE_sub {L : Lay} (hL : L.Ok) :
    Region.Sub ⟨State.addr (L.SP - BitVec.ofNat 32 8) - BitVec.ofNat 64 28, 28⟩ L.STK := by
  rw [addr_sub (by have := hL.nSP; omega), BitVec.sub_sub, BitVec.ofNat_add_ofNat]
  exact Offset.sub_below _ (by omega) (by omega)

theorem argR_sub {L : Lay} {t : State} (ht : t.sp = L.SP) : Region.Sub (argR t) L.STK := by
  simp only [argR, ht]; exact Offset.sub_below _ (by omega) (by omega)

/-- The regions the signing function on `μ` reads and writes. -/
abbrev signRd (p : Params) (s : State) : List Region :=
  [⟨State.addr (s.gpr .r0), p.skLen⟩, ⟨(slay p s).MU, 64⟩, ⟨State.addr (stackArg s 1), 32⟩]
abbrev signWr (p : Params) (s : State) : List Region :=
  [⟨State.addr (stackArg s 2), p.sigLen⟩, ⟨State.addr (stackArg s 3), sScr p⟩]

/-- The registers after the moves of the arguments. -/
theorem signRegs_of (hL : (slay p s).Ok) {g : Reg → BitVec 32} {m₀ : Mem} {t t1 : State}
    (hc : Ctx (slay p s) g m₀ t) (hm : (∀ da ∈ signArgs, t1.gpr da.1 = da.2.val t)) :
    t1.gpr .r0 = s.gpr .r0 ∧ t1.gpr .r1 = (slay p s).X32 + BitVec.ofNat 32 840 ∧ t1.gpr .r2 = stackArg s 1 ∧
      t1.gpr .r3 = stackArg s 2 ∧ t1.gpr .r12 = stackArg s 3 := by
  have e0 := hm (.r0, .slot fKey) (by simp)
  have e1 := hm (.r1, .off oMU) (by simp)
  have e2 := hm (.r2, .slot fRnd) (by simp)
  have e3 := hm (.r3, .slot fSig) (by simp)
  have e4 := hm (.r12, .slot fScr) (by simp)
  rw [hc.slotV hL (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  rw [hc.slotV hL (f := fRnd) (j := 5) rfl (by omega)] at e2
  rw [hc.slotV hL (f := fSig) (j := 6) rfl (by omega)] at e3
  rw [hc.slotV hL (f := fScr) (j := 7) rfl (by omega)] at e4
  simp only [Lay.vals, slay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3 e4
  exact ⟨e0, e1, e2, e3, e4⟩

/-- The precondition of the signing function on `μ`, on entry to it. -/
theorem signK_pre (hp : p ∈ params) (h : SPre p s) (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32}
    {m₀ : Mem} {t t1 : State} (hc : Ctx (slay p s) g m₀ t)
    (hA : ∀ da ∈ signArgs, t1.gpr da.1 = da.2.val t) (hsp1 : t1.sp = s.sp) :
    (signContract p Arm.abi 28).pre
      ((pushed [.r12, .lr] t1).callEntry.withRegions (signRd p s ++ [argR t1]) (signWr p s)) := by
  have hL := slay_ok hp h h8
  obtain ⟨e0, e1, e2, e3, e4⟩ := signRegs_of hL hc hA
  have h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := h.sp; omega
  obtain ⟨a0, a1, -⟩ := push2_arg (t := (pushed [.r12, .lr] t1).callEntry.withRegions (signRd p s ++ [argR t1])
    (signWr p s)) h8' rfl rfl
  have hmu := mu_eq hL
  have hsub := sScr_sub p (State.addr (stackArg s 3))
  have hmuS : Region.Sub ⟨(slay p s).MU, 64⟩ ⟨State.addr (stackArg s 3), mScrLen p⟩ := (mu_within hL).sub
  have eSP : ((pushed [.r12, .lr] t1).callEntry.withRegions (signRd p s ++ [argR t1]) (signWr p s)).sp =
      s.sp - BitVec.ofNat 32 8 := by
    simp only [State.withRegions_sp, State.callEntry_sp, VG.Arm.pushed_sp, hsp1]; rfl
  have kE := stkE_sub (L := slay p s) hL
  have kA := argR_sub (L := slay p s) (t := t1) hsp1
  simp only [slay] at kE kA
  have hstk : ∀ {r : Region}, (rStk s).Disjoint r → Region.Disjoint ⟨State.addr (s.sp - BitVec.ofNat 32 8) -
      BitVec.ofNat 64 28, 28⟩ r := fun hr => hr.sub_left kE
  refine signC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [view_gpr _ _ _ _ (by decide : Reg.r0 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r1 ∉ linkRegs),
      view_gpr _ _ _ _ (by decide : Reg.r2 ∉ linkRegs), view_gpr _ _ _ _ (by decide : Reg.r3 ∉ linkRegs),
      e0, e1, e2, e3, a0, a1, e4, eSP, hmu, State.withRegions_rd, State.withRegions_wr]
  · rw [sp_sub8 (by have := h.sp; omega)]; have := h.sp; omega
  · rw [sp_sub8 (by have := h.sp; omega)]; have := h.spA; omega
  · simp only [argR, hsp1, List.cons_append, List.nil_append]
  · exact h.skSig
  · exact h.skScr.sub_right hsub
  · exact h.sigScr.symm.sub_left hmuS
  · exact (x_sScr hL rfl (by omega) : Region.Disjoint ⟨(slay p s).X + BitVec.ofNat 64 840, 64⟩ _)
  · exact h.rndSig
  · exact h.rndScr.sub_right hsub
  · exact h.sigScr.sub_right hsub
  · exact (h.stkSig.sub_left kA).symm
  · exact ((h.stkScr.sub_left kA).sub_right hsub).symm
  · exact hstk h.stkSk
  · exact (k_mu hL).sub_left kE
  · exact hstk h.stkRnd
  · exact hstk h.stkSig
  · exact hstk (h.stkScr.sub_right hsub)
  · rw [hsp1, addr_sub (by have := h.sp; omega)]
    exact (Offset.base_disjoint_below _ (by omega)).symm
  · exact h.nSk
  · have := hL.x32_lt
    rw [x32_toNat hL (by omega)]; omega
  · exact h.nRnd
  · exact h.nSig
  · have := h.nScr; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega

/-- The bytes of a region apart from the 8 the push writes, in the callee's entry state. -/
theorem pushed_bytes {t : State} (h8 : 8 ≤ t.sp.toNat) (rd wr : List Region) {a : Addr} {n : Nat}
    (hd : Region.Disjoint ⟨a, n⟩ (below t 8)) (hn : n ≤ 2 ^ 64) :
    bytesAt ((pushed [.r12, .lr] t).callEntry.withRegions rd wr).mem a n = bytesAt t.mem a n := by
  simp only [State.withRegions_mem, State.callEntry_mem]
  exact Proof.MlKem.bytesAt_frame (push2_frame h8) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hd) hn

/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) (h : SPre p s)
    (h8 : (stackArg s 0).toNat < 256) {g : Reg → BitVec 32} {m₀ : Mem} {t : State}
    (hc : Ctx (slay p s) g m₀ t) :
    WP isa (.seq (.block (setArgs signArgs)) (.frame (.push [.r12, .lr]) (.call n c) (.pop .r12 8))) t fun s' =>
      Fin (slay p s) g s' ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (State.addr (s.gpr .r0)) p.skLen) (bytesAt t.mem (slay p s).MU 64)
          (bytesAt t.mem (State.addr (stackArg s 1)) 32)) (s'.gpr .r0)
        (bytesAt s'.mem (State.addr (stackArg s 2)) p.sigLen) := by
  have hL := slay_ok hp h h8
  refine WP.seq (WP.mono (setArgs_ok signArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx (slay p s) g m₀ t1 := hc.regs o.rd o.wr o.sp o.mem fun r hr hl =>
    o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr hl _)
  obtain ⟨e0, e1, e2, e3, _⟩ := signRegs_of hL hc hA
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hpre := signK_pre hp h h8 hc hA hsp1
  have hsub := sScr_sub p (State.addr (stackArg s 3))
  have hmuS : Region.Sub ⟨(slay p s).MU, 64⟩ ⟨State.addr (stackArg s 3), mScrLen p⟩ := (mu_within hL).sub
  refine WP.mono (frameCall_ok (D := 36) hS.ver.1 (by have := hS.su; omega) (by rw [hsp1]; exact h.sp) hpre ?_ ?_)
    fun s' ⟨hrd, hwr, hsp, hcs, hf, s₂, hm₂, hg₂, hpost⟩ => ?_
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, by simp [slay, h.rd], within_self _⟩
    · exact ⟨_, by simp [slay, h.wr], mu_within hL⟩
    · exact ⟨_, by simp [slay, h.rd], within_self _⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [slay, h.wr], within_self _⟩
    · exact ⟨⟨State.addr (stackArg s 3), mScrLen p⟩, by simp [slay, h.wr],
        within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 4 ≤ 120 → s'.mem.readW ((slay p s).X + BitVec.ofNat 64 (904 + d)) 32 =
      t1.mem.readW ((slay p s).X + BitVec.ofNat 64 (904 + d)) 32 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact h.sigScr.symm.sub_left ((within_off (slay p s).X (d := 904 + d) (n := 4) (k := 1024)
          (by omega)).trans hL.xs_sc).sub
      · exact x_sScr hL rfl (by omega)
      · rw [hsp1]
        exact hL.sv_disj (r := belowA s.sp 36) (.inr fun _ h => h) hd') (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .r7 (by decide) (by decide)).trans hc1.r7,
    fun r hr h7 hl => (hcs r hr hl).trans (hc1.cs r hr h7 hl),
    (hsv 0 (by omega)).trans hc1.s7, (hsv 4 (by omega)).trans hc1.sLR⟩, ?_⟩
  have h8' : 8 ≤ t1.sp.toNat := by rw [hsp1]; have := h.sp; omega
  have kA := argR_sub (L := slay p s) (t := t1) hsp1
  have bk : Region.Sub (below t1 8) (slay p s).STK := below_stk hsp1
  sig_reduce [signContract, signSig, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val] at hpost
  have pm : ∀ (x : BitVec 32) (n : Nat), Region.Disjoint ⟨State.addr x, n⟩ (below t1 8) → n ≤ 2 ^ 64 →
      bytesAt (storeWords t1.mem (t1.sp - 8#32) [t1.gpr .r12, t1.gpr .lr]) (BitVec.setWidth 64 x) n =
        bytesAt t1.mem (State.addr x) n := fun x n hd hn =>
    Proof.MlKem.bytesAt_frame (push2_frame h8') (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hd) hn
  rw [e0, e1, e2, e3, pm _ _ (h.stkSk.symm.sub_right bk) (by have := h.nSk; omega),
    pm _ _ (by rw [mu_eq hL]; exact (k_mu hL).symm.sub_right bk) (by decide),
    pm _ _ (h.stkRnd.symm.sub_right bk) (by decide), mu_eq hL, hm₂, Proof.MlKem.Arm.setWidth_append32,
    hg₂ .r0 (by decide), o.mem] at hpost
  exact hpost

end

end VG.Proof.MlDsa.Arm.Message
