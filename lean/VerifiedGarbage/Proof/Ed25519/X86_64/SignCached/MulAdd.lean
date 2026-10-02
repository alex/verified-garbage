import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified

/-! The final scalar multiply-add in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarMulAdd)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base within_off gpr_ce rsp_ce sub8 ea_stk add_add sx32 ce_byte)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def MulArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out + BitVec.ofNat 64 32 ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
    t.gpr .rdx = L.B + BitVec.ofNat 64 112 ∧ t.gpr .rcx = L.B + BitVec.ofNat 64 16 ∧ t.gpr .r8 = L.scr

theorem mulArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block mulAddArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ MulArgs L t' := by
  have hs := hc.inFr (d := 216) (by omega) (by omega)
  have ho := hc.inFr (d := 256) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [mulAddArgs, framePtr, fOut, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hs, ho, Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, MulArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, rfl,
    by rw [sx32 (by decide : 64 < 2 ^ 31), add_add],
    by rw [sx32 (by decide : 96 < 2 ^ 31), add_add],
    by rw [sx32 (by decide : 0 < 2 ^ 31), BitVec.add_zero], trivial⟩

abbrev mulRd (L : Lay) : List Region :=
  [⟨L.B + BitVec.ofNat 64 80, 32⟩, ⟨L.B + BitVec.ofNat 64 112, 32⟩, ⟨L.B + BitVec.ofNat 64 16, 32⟩]
abbrev mulWr (L : Lay) : List Region := [⟨L.out + BitVec.ofNat 64 32, 32⟩, L.SCR]

theorem mul_regs {t : State} (ha : MulArgs L t) (rd wr : List Region) :
    MulArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.2.2⟩

theorem mul_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : MulArgs L t) :
    scalarMulAddLocal.pre (t.callEntry.withRegions (mulRd L) (mulWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx, h8⟩ := mul_regs ha (mulRd L) (mulWr L)
  simp only [scalarMulAddLocal, rsp_ce, hdi, hsi, hdx, hcx, h8, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 112) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 16) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    (hL.ko.sub_left (Offset.sub_base L.B (d := 8) (n := 8) (by decide))).sub_right
      (Offset.sub_base L.out (d := 32) (n := 32) (by decide)),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega), hL.nc,
    hL.oc.sub_left (Offset.sub_base L.out (d := 32) (n := 32) (by decide))⟩

theorem mul_call (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : MulArgs L t) :
    WP isa (.call "vg_ed25519_scalar_mul_add" scalarMulAdd) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem (L.out + BitVec.ofNat 64 32) 32 = Spec.Ed25519.scalarMulAdd
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 112) 32)
        (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) ∧
      Frame (mulWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL scalarMulAdd_ok (Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide))
    (by lit_decide) hc (mul_pre hL hc ha) ?_ ?_
    fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  · intro r hr
    simp only [mulRd, mulWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact ⟨L.FR, by simp, 64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, 96, by rw [add_add], by show 96 + 32 ≤ 248; decide⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.OUT, by simp, within_off _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [mulWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr (.inl (within_off _ (by omega)))
    · exact .inr (.inr (within_base _ (by omega)))
  · obtain ⟨hdi, hsi, hdx, hcx, -⟩ := mul_regs ha (mulRd L) (mulWr L)
    change Spec.Ed25519.bytesAt s₂.mem _ 32 = Spec.Ed25519.scalarMulAdd _ _ _ at hpost
    rw [hdi, hsi, hdx, hcx, State.withRegions_mem, hm] at hpost
    have he (d : Nat) (hd : 16 ≤ d) (hn : d + 32 ≤ 264) :
        Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 d) 32 =
          Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 d) 32 := by
      apply List.map_congr_left
      intro i hi
      exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 d, 32⟩) (i := i)
        (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide : 32 ≤ 2 ^ 64) (List.mem_range.mp hi)
    rw [he 80 (by decide) (by decide), he 112 (by decide) (by decide), he 16 (by decide) (by decide)] at hpost
    exact hpost

end VG.Proof.Ed25519.X86_64.SignCached
