import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Hash
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base

/-! Reduce the challenge and place its 64-byte encoding outside scratch. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce stk)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 ea_stk add_add sx32)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def ReduceArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
    t.gpr .rdx = L.scr

theorem reduceArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block reduceArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ ReduceArgs L t' := by
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [reduceArgs, fScratch, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h144,
    Option.some.injEq, exists_eq_left', hc.pScr, ReduceArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial,
    by rw [show (64 : BitVec 32).signExtend 64 = BitVec.ofNat 64 64 from rfl, add_add], trivial⟩

abbrev reduceRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 80, 64⟩]
abbrev reduceWr (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 32⟩, L.SCR]

theorem reduce_regs {t : State} (ha : ReduceArgs L t) (rd wr : List Region) :
    ReduceArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem reduce_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L t) :
    scalarReduceLocal.pre (t.callEntry.withRegions (reduceRd L) (reduceWr L)) := by
  obtain ⟨hdi, hsi, hdx⟩ := reduce_regs ha (reduceRd L) (reduceWr L)
  simp only [scalarReduceLocal, rsp_ce, hdi, hsi, hdx, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 64) (e := 0) (k := 8192) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega)⟩

theorem reduce_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L t)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 64 = digest) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32 = Spec.Ed25519.scalarReduce digest := by
  refine call_ok hL scalarReduce_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (reduce_pre hL hc ha) ?_ ?_
    fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  · intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 64 ≤ 168; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl (within_base _ (by omega))
    · exact .inr (within_base _ (by omega))
  · obtain ⟨hdi, hsi, -⟩ := reduce_regs ha (reduceRd L) (reduceWr L)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt _ _ 64) at hpost
    rw [hdi, hsi, State.withRegions_mem, hm] at hpost
    have he : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 80) 64 =
        Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 64 := by
      apply List.map_congr_left
      intro i hi
      exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 80, 64⟩) (i := i) (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)
    rw [he, hh] at hpost
    exact hpost

/-- Stores in the upper half of the challenge preserve the saved arguments. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t)
    (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hmx : t'.mxcsr = t.mxcsr)
    (hg : t'.gpr = t.gpr) (hf : Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] t.mem t'.mem) :
    Ctx L g mx m₀ t' := by
  have keep : ∀ d, 144 ≤ d → d + 8 ≤ 184 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 := by
    intro d h₁ h₂
    exact hf.readW (Region.contains_self _ _) (by
      intro r hr
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, by rw [hg]; exact hc.rsp,
    fun r hr h => by rw [hg]; exact hc.cs r hr h, by rw [hmx]; exact hc.mx,
    (keep 144 (by omega) (by omega)).trans hc.pScr,
    (keep 152 (by omega) (by omega)).trans hc.pSig,
    (keep 160 (by omega) (by omega)).trans hc.pLen,
    (keep 168 (by omega) (by omega)).trans hc.pMsg,
    (keep 176 (by omega) (by omega)).trans hc.pPk,
    hc.frame.trans (Frame.sub hf ?_)⟩
  intro r hr
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨L.STK, by simp, Offset.sub_base _ (by decide)⟩

theorem extend_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block extendChallenge) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 48, 32⟩] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = 0 ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 56) 64 = 0 ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 64) 64 = 0 ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 72) 64 = 0 := by
  have w0 := hc.inFrW (d := 48) (by omega) (by omega)
  have w1 := hc.inFrW (d := 56) (by omega) (by omega)
  have w2 := hc.inFrW (d := 64) (by omega) (by omega)
  have w3 := hc.inFrW (d := 72) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [extendChallenge, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32,
    State.setReg32, State.store64, BitVec.xor_self, BitVec.setWidth_zero, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.wr_setReg, RegUpd.wr_arithFlags, RegUpd.mem_setReg, RegUpd.mem_arithFlags,
    reduceCtorEq, ite_false, ite_true, ea_stk, hc.rsp, add_add, Nat.reduceAdd,
    w0, w1, w2, w3, Option.bind_some, Option.some.injEq, exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := PublicKey.four_ok (L.B + BitVec.ofNat 64 32) t.mem 0 0 0 0
  simp only [add_add, Nat.reduceAdd] at hf h0 h1 h2 h3
  have hz := hc.regs (t' := (arithFlags t (0 : BitVec 32) false false).setReg .rax 0) rfl rfl rfl rfl (by cs_tac)
  exact ⟨hz.store rfl rfl rfl rfl hf, hf, h0, h1, h2, h3⟩

end VG.Proof.Ed25519.X86_64.VerifyMessage
