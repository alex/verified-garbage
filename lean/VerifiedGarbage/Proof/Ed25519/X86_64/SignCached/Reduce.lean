import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Hash
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base

/-! Reduce a digest into the nonce or challenge slot. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarReduce stk)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 ea_stk add_add sx32)
variable {out : Nat} {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def ReduceArgs (L : Lay) (out : Nat) (t : State) : Prop :=
  t.gpr .rdi = L.B + BitVec.ofNat 64 (16 + out) ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 144 ∧
    t.gpr .rdx = L.scr

theorem reduceArgs_ok {t : State} (hc : Ctx L g mx m₀ t) (ho : out + 32 ≤ 128) :
    WP isa (.block (reduceArgs out)) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ ReduceArgs L out t' := by
  have h216 := hc.inFr (d := 216) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [reduceArgs, framePtr, fScratch, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, h216,
    Option.some.injEq, exists_eq_left', hc.pScr, ReduceArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, by rw [sx32 (by omega), add_add],
    by rw [sx32 (by decide : 128 < 2 ^ 31), add_add], trivial⟩

abbrev reduceRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 144, 64⟩]
abbrev reduceWr (L : Lay) (out : Nat) : List Region := [⟨L.B + BitVec.ofNat 64 (16 + out), 32⟩, L.SCR]

theorem reduce_regs {t : State} (ha : ReduceArgs L out t) (rd wr : List Region) :
    ReduceArgs L out (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem reduce_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L out t) (ho : out + 32 ≤ 128) :
    scalarReduceLocal.pre (t.callEntry.withRegions (reduceRd L) (reduceWr L out)) := by
  obtain ⟨hdi, hsi, hdx⟩ := reduce_regs ha (reduceRd L) (reduceWr L out)
  simp only [scalarReduceLocal, rsp_ce, hdi, hsi, hdx, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 144) (n := 64) (e := 0) (k := 8192) (by omega) (by omega),
    Offset.disjoint _ (by omega) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 16 + out) (n := 32) (e := 0) (k := 8192) (by omega) (by omega)⟩

theorem reduce_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : ReduceArgs L out t) (ho : out + 32 ≤ 128)
    {digest : List Byte} (hh : Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 = digest) :
    WP isa (.call "vg_ed25519_scalar_reduce" scalarReduce) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 (16 + out)) 32 = Spec.Ed25519.scalarReduce digest ∧
      Frame (reduceWr L out ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL scalarReduce_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (reduce_pre hL hc ha ho) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [reduceRd, reduceWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 128, by rw [add_add], by show 128 + 64 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, out, by rw [add_add], by change out + 32 ≤ 248; omega⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [reduceWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inl ⟨out, by rw [add_add], by change out + 32 ≤ 192; omega⟩
    · exact .inr (.inr (within_base _ (by omega)))
  · obtain ⟨hdi, hsi, -⟩ := reduce_regs ha (reduceRd L) (reduceWr L out)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarReduce (Spec.Ed25519.bytesAt _ _ 64) at hpost
    rw [hdi, hsi, State.withRegions_mem, hm] at hpost
    have he : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 144) 64 =
        Spec.Sha512.bytesAt t.mem (L.B + BitVec.ofNat 64 144) 64 := by
      apply List.map_congr_left
      intro i hi
      exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 144, 64⟩) (i := i) (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)
    rw [he, hh] at hpost
    exact hpost

end VG.Proof.Ed25519.X86_64.SignCached
