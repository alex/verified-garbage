import VerifiedGarbage.Proof.Ed25519.X86_64.SignCached.Args
import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Base

/-! The nonce's base-point multiplication in complete signing. -/
namespace VG.Proof.Ed25519.X86_64.SignCached
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (scalarBaseName scalarBase_precomputed)
open VG.Impl.Ed25519.X86_64.SignCached
open VG.Proof.Ed25519.X86_64.PublicKey
  (Within within_base gpr_ce rsp_ce sub8 ea_stk add_add sx32 ce_byte)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 80 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block baseArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' := by
  have hs := hc.inFr (d := 216) (by omega) (by omega)
  have ho := hc.inFr (d := 256) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [baseArgs, framePtr, fOut, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, hs, ho, Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial,
    by rw [sx32 (by decide : 64 < 2 ^ 31), add_add], trivial⟩

theorem base_nosp : NoSp scalarBase_precomputed :=
  Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)

theorem base_depth : scalarBase_precomputed.depth ≤ 1 := by lit_decide

abbrev baseRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 80, 32⟩]
abbrev baseWr (L : Lay) : List Region := [⟨L.out, 32⟩, L.SCR]

theorem base_regs {t : State} (ha : BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 80 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem base_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    Proof.Ed25519.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := base_regs ha (baseRd L) (baseWr L)
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, g3, rsp_ce, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial,
    by simpa using hL.stk_scr (d := 80) (n := 32) (e := 0) (k := 8192) (by omega) (by omega),
    (hL.ko.sub_left (Offset.sub_base L.B (d := 8) (n := 8) (by decide))).sub_right
      (within_base L.out (by decide : 32 ≤ 64)).sub,
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega), hL.nc⟩

theorem base_sub : ∀ r ∈ baseRd L ++ baseWr L, ∃ R ∈ L.inputs ++ [L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, ⟨64, by rw [add_add], by show 64 + 32 ≤ 248; decide⟩⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem base_wsub : ∀ r ∈ baseWr L, Within r L.DATA ∨ Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inr (.inl (within_base _ (by omega)))
  · exact .inr (.inr (within_base _ (by omega)))

theorem base_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) {scalar : List Byte}
    (hs : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 = scalar) :
    WP isa (.call scalarBaseName scalarBase_precomputed) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 =
        Spec.Ed25519.scalarBase scalar ∧ Frame (baseWr L ++ [⟨L.B, 16⟩]) t.mem t'.mem := by
  refine call_ok hL Proof.Ed25519.X86_64.scalarBase_precomputed_ok base_nosp base_depth hc
    (base_pre hL hc ha) base_sub base_wsub fun s' hc' hf _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_, hf⟩
  obtain ⟨g1, g2, -⟩ := base_regs ha (baseRd L) (baseWr L)
  have h := hpost
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 80) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 80) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 80, 32⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by show (32 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, hs]

end VG.Proof.Ed25519.X86_64.SignCached
