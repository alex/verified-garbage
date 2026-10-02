import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Pre
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

/-!
# ML-DSA on AArch64, `sign_message`: the call of the signing function on `μ`

Untrusted: everything here is checked by Lean. Any code verified against
`signContract p AArch64.abi 16` whose frames nest at most once (`SignFn`):
its call on the key, `μ` at `X + 840`, `rnd`, `sig` and the first
`scratchWords p` words of `scratch` (`signCall_ok`), after which the saves
are intact (`Fin`).
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

/-- A signing function on `μ` that `sign_message` can call. -/
structure SignFn (p : Params) (c : Prog isa) : Prop where
  ver : Verified AArch64.target c (signContract p AArch64.abi 16)
  dle : DLe 1 c

/-- The size of the working space of the signing function on `μ`. -/
abbrev sScr (p : Params) : Nat := scratchWords p * 8

/-- The precondition of `signContract p AArch64.abi 16`, from its facts. -/
theorem signC_pre {p : Params} {s : State} (sp : 16 ≤ s.sp.toNat)
    (rd : s.rd = [⟨s.gpr .x0, p.skLen⟩, ⟨s.gpr .x1, 64⟩, ⟨s.gpr .x2, 32⟩])
    (wr : s.wr = [⟨s.gpr .x3, p.sigLen⟩, ⟨s.gpr .x4, sScr p⟩])
    (d03 : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d04 : Region.Disjoint ⟨s.gpr .x0, p.skLen⟩ ⟨s.gpr .x4, sScr p⟩)
    (d13 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d14 : Region.Disjoint ⟨s.gpr .x1, 64⟩ ⟨s.gpr .x4, sScr p⟩)
    (d23 : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x3, p.sigLen⟩)
    (d24 : Region.Disjoint ⟨s.gpr .x2, 32⟩ ⟨s.gpr .x4, sScr p⟩)
    (d34 : Region.Disjoint ⟨s.gpr .x3, p.sigLen⟩ ⟨s.gpr .x4, sScr p⟩)
    (k0 : (rStk s).Disjoint ⟨s.gpr .x0, p.skLen⟩) (k1 : (rStk s).Disjoint ⟨s.gpr .x1, 64⟩)
    (k2 : (rStk s).Disjoint ⟨s.gpr .x2, 32⟩) (k3 : (rStk s).Disjoint ⟨s.gpr .x3, p.sigLen⟩)
    (k4 : (rStk s).Disjoint ⟨s.gpr .x4, sScr p⟩)
    (n0 : (s.gpr .x0).toNat + p.skLen ≤ 2 ^ 64) (n1 : (s.gpr .x1).toNat + 64 ≤ 2 ^ 64)
    (n2 : (s.gpr .x2).toNat + 32 ≤ 2 ^ 64) (n3 : (s.gpr .x3).toNat + p.sigLen ≤ 2 ^ 64)
    (n4 : (s.gpr .x4).toNat + sScr p ≤ 2 ^ 64) :
    (signContract p AArch64.abi 16).pre s := by
  sig_pre [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop]
  exact ⟨sp, rd, wr, d03, d04, d13, d14, d23, d24, d34, k0, k1, k2, k3, k4, n0, n1, n2, n3, n4⟩

/-- The arguments of the call of the signing function on `μ`. -/
abbrev signArgs : List (Reg × Arg) := [(.x0, .slot fKey), (.x1, .off oMU), (.x2, .slot fRnd), (.x3, .slot fSig),
  (.x4, .slot fScr)]

section
variable {p : Params} {s : State}

theorem gpr_ce (t : State) {r : Reg} (h : r ∉ linkRegs := by decide) :
    (t.callEntry.withRegions rd wr).gpr r = t.gpr r := by
  rw [State.withRegions_gpr, State.callEntry_gpr _ h]

/-- The working space of the signing function on `μ`: the start of `scratch`. -/
theorem sScr_sub (p : Params) (s : State) :
    Region.Sub ⟨s.gpr .x7, sScr p⟩ ⟨s.gpr .x7, mScrLen p⟩ :=
  Region.sub_prefix (by rw [mScr_eq]; simp only [sScr, oE]; omega)

/-- The saves are apart from it. -/
theorem sv_sScr {p : Params} (hp : p ∈ params) (s : State) {d n : Nat} (hd : d + n ≤ 88) :
    Region.Disjoint ⟨(slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ ⟨s.gpr .x7, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 904 + BitVec.ofNat 64 d, n⟩ _
  rw [add_add, add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega) (by omega)

theorem mu_sScr {p : Params} (hp : p ∈ params) (s : State) :
    Region.Disjoint ⟨(slay p s).MU, 64⟩ ⟨s.gpr .x7, sScr p⟩ := by
  show Region.Disjoint ⟨s.gpr .x7 + BitVec.ofNat 64 (oE p) + BitVec.ofNat 64 840, 64⟩ _
  rw [add_add]
  have := oE_lt hp
  exact Offset.disjoint_base _ (by simp only [sScr, oE]; omega) (by omega)

theorem mu_within (p : Params) (s : State) : Within ⟨(slay p s).MU, 64⟩ ⟨s.gpr .x7, mScrLen p⟩ :=
  (within_off (slay p s).X (d := 840) (n := 64) (k := 1024) (by omega)).trans (slay_X p s)

theorem mu_nowrap {L : Lay} (hL : L.Ok) : L.MU.toNat + 64 ≤ 2 ^ 64 := by
  have := hL.nX
  show (L.X + BitVec.ofNat 64 840).toNat + 64 ≤ 2 ^ 64
  rw [toNat_add_ofNat (by omega)]; omega

/-- The call of the signing function on `μ`. -/
theorem signCall_ok {n : String} {c : Prog isa} (hS : SignFn p c) (hp : p ∈ params) (h : SPre p s)
    (h8 : (s.gpr .x4).toNat < 256) {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t : State}
    (hc : Ctx (slay p s) g vv m₀ t) :
    WP isa (callA n c signArgs) t fun s' => Fin (slay p s) g vv s' ∧
      Outcome (fun b => signMu p b (bytesAt t.mem (s.gpr .x0) p.skLen) (bytesAt t.mem (slay p s).MU 64)
          (bytesAt t.mem (s.gpr .x5) 32)) ((s'.gpr .x0).setWidth 32) (bytesAt s'.mem (s.gpr .x6) p.sigLen) := by
  have hL := slay_ok hp h h8
  refine WP.seq (WP.mono (setArgs_ok signArgs (by decide) t (hc.xOk hL)) fun t1 ⟨hA, o⟩ => ?_)
  have hc1 : Ctx (slay p s) g vv m₀ t1 :=
    hc.regs o.rd o.wr o.sp o.mem o.vcs fun r hr _ => o.gpr r (by simp only [List.map_cons, List.map_nil]; exact not_pres hr _)
  have e0 := hA (.x0, .slot fKey) (by simp)
  have e1 := hA (.x1, .off oMU) (by simp)
  have e2 := hA (.x2, .slot fRnd) (by simp)
  have e3 := hA (.x3, .slot fSig) (by simp)
  have e4 := hA (.x4, .slot fScr) (by simp)
  rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)] at e0
  rw [hc.off] at e1
  replace e1 : t1.gpr .x1 = (slay p s).MU := e1
  rw [hc.slotV (f := fRnd) (j := 5) rfl (by omega)] at e2
  rw [hc.slotV (f := fSig) (j := 6) rfl (by omega)] at e3
  rw [hc.slotV (f := fScr) (j := 7) rfl (by omega)] at e4
  simp only [Lay.vals, slay, List.getD_cons_zero, List.getD_cons_succ] at e0 e2 e3 e4
  have hsp1 : t1.sp = s.sp := hc1.sp
  have hmu := (mu_within p s).sub
  have hsub := sScr_sub p s
  have hd := hS.dle.1
  have hstk : ∀ {rd wr : List Region} {r : Region}, (rStk s).Disjoint r →
      (rStk (t1.callEntry.withRegions rd wr)).Disjoint r := by
    intro rd wr r hr; simpa [rStk, hsp1] using hr
  have hpre : (signContract p AArch64.abi 16).pre (t1.callEntry.withRegions
      [⟨s.gpr .x0, p.skLen⟩, ⟨(slay p s).MU, 64⟩, ⟨s.gpr .x5, 32⟩] [⟨s.gpr .x6, p.sigLen⟩, ⟨s.gpr .x7, sScr p⟩]) := by
    refine signC_pre ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      try simp only [gpr_ce t1 (r := .x0), gpr_ce t1 (r := .x1), gpr_ce t1 (r := .x2), gpr_ce t1 (r := .x3),
        gpr_ce t1 (r := .x4), e0, e1, e2, e3, e4, State.withRegions_rd, State.withRegions_wr]
    · simp only [State.withRegions_sp, State.callEntry_sp, hsp1]; exact h.sp
    · exact h.skSig
    · exact h.skScr.sub_right hsub
    · exact h.sigScr.symm.sub_left hmu
    · exact mu_sScr hp s
    · exact h.rndSig
    · exact h.rndScr.sub_right hsub
    · exact h.sigScr.sub_right hsub
    · exact hstk h.stkSk
    · have km := k_mu hL
      exact hstk km
    · exact hstk h.stkRnd
    · exact hstk h.stkSig
    · exact hstk (h.stkScr.sub_right hsub)
    · exact h.nSk
    · exact mu_nowrap hL
    · exact h.nRnd
    · exact h.nSig
    · have := h.nScr; simp only [mScrLen, sScr, messageScratchWords] at this ⊢; omega
  refine WP.callFV hS.ver.1 hpre ?_ ?_ (fun s' hrd hwr hsp hf hcs hvs hpost => ?_) (by omega)
  · rw [hc1.rd, hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, by simp [slay, h.rd], within_self _⟩
    · exact ⟨_, by simp [slay, h.wr], mu_within p s⟩
    · exact ⟨_, by simp [slay, h.rd], within_self _⟩
    · exact ⟨_, by simp [slay, h.wr], within_self _⟩
    · exact ⟨⟨s.gpr .x7, mScrLen p⟩, by simp [slay, h.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  · rw [hc1.wr]
    refine covers_of_within fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, by simp [slay, h.wr], within_self _⟩
    · exact ⟨⟨s.gpr .x7, mScrLen p⟩, by simp [slay, h.wr], within_base _ (by rw [mScr_eq]; simp only [sScr, oE]; omega)⟩
  -- After the call.
  have hsv : ∀ d, d + 8 ≤ 88 → s'.mem.readW ((slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 =
      t1.mem.readW ((slay p s).X + BitVec.ofNat 64 904 + BitVec.ofNat 64 d) 64 := fun d hd' =>
    hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [add_add]
        exact (h.sigScr.symm.sub_left ((within_off (slay p s).X (d := 904 + d) (n := 8) (k := 1024)
          (by omega)).trans (slay_X p s)).sub)
      · exact sv_sScr hp s hd'
      · rw [hsp1]
        exact (hL.sv_disj (r := below s.sp (16 * c.aarch64Depth)) (.inr (below_sub (by omega) (by decide))) hd'))
      (by decide)
  refine ⟨⟨hrd.trans hc1.rd, hwr.trans hc1.wr, hsp.trans hc1.sp, (hcs .x28 (by decide) (by decide)).trans hc1.x28,
    fun r hr h28 h30 => (hcs r hr h30).trans (hc1.cs r hr h28 h30), fun r hr => (hvs r hr).trans (hc1.vs r hr),
    (hsv 0 (by omega)).trans hc1.s28, (hsv 8 (by omega)).trans hc1.s30⟩, ?_⟩
  sig_reduce [signContract, signSig, AArch64.abi, AArch64.argRegs, List.range, List.range.loop] at hpost
  simp only [e0, e1, e2, e3, o.mem] at hpost
  exact hpost

end

end VG.Proof.MlDsa.AArch64.Message
