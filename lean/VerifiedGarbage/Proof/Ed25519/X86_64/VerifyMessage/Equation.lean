import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Reduce
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.Encoding
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyVerified

/-! Connect the reduced challenge to the verified group equation. -/
namespace VG.Proof.Ed25519.X86_64.VerifyMessage

variable {fld : VG.Impl.Ed25519.X86_64.Arith} [VG.Proof.Ed25519.X86_64.EdArith fld] {fs : String}
variable {dbl : VG.Prog VG.X86_64.isa} [VG.Proof.Ed25519.X86_64.EdDouble dbl]
open VG VG.X86_64
open VG.Impl.Ed25519.X86_64 (verifyEquation)
open VG.Impl.Ed25519.X86_64.VerifyMessage
open VG.Proof.Ed25519.X86_64.PublicKey
  (within_base gpr_ce rsp_ce sub8 ea_stk add_add)
variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

def EqArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.pk ∧ t.gpr .rsi = L.sig ∧ t.gpr .rdx = L.B + BitVec.ofNat 64 16 ∧
    t.gpr .rcx = L.scr

theorem equationArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block equationArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ EqArgs L t' := by
  have h144 := hc.inFr (d := 144) (by omega) (by omega)
  have h152 := hc.inFr (d := 152) (by omega) (by omega)
  have h176 := hc.inFr (d := 176) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [equationArgs, fScratch, fSignature, fPublicKey,
    runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, h144, h152, h176, Option.some.injEq, exists_eq_left', hc.pScr, hc.pSig, hc.pPk, EqArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial⟩

abbrev eqRd (L : Lay) : List Region := [L.PK, L.SIG, ⟨L.B + BitVec.ofNat 64 16, 64⟩]
abbrev eqWr (L : Lay) : List Region := [L.SCR]

theorem eq_regs {t : State} (ha : EqArgs L t) (rd wr : List Region) :
    EqArgs L (t.callEntry.withRegions rd wr) :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2.1, (gpr_ce _ _ _ (by decide)).trans ha.2.2.2⟩

theorem eq_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : EqArgs L t) :
    verifyLocal.pre (t.callEntry.withRegions (eqRd L) (eqWr L)) := by
  obtain ⟨hdi, hsi, hdx, hcx⟩ := eq_regs ha (eqRd L) (eqWr L)
  simp only [verifyLocal, rsp_ce, hdi, hsi, hdx, hcx, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, hL.sc L.PK (by simp [Lay.inputs]), hL.sc L.SIG (by simp [Lay.inputs]),
    by simpa using hL.stk_scr (d := 16) (n := 64) (e := 0) (k := 8192) (by omega) (by omega),
    by simpa using hL.stk_scr (d := 8) (n := 8) (e := 0) (k := 8192) (by omega) (by omega), hL.nc⟩

/-- What the call of the equation checker `c` needs of its code, beyond its
correctness: it restores MXCSR (`ctlOk`), writes `rsp` only as calls and
returns do, nests no calls, and writes no stack pointer. Decided for each
checker in the registration file. -/
structure EqCode (c : Prog isa) : Prop where
  mx : VG.Proof.Ed25519.X86_64.MxcsrOk c
  noSp : c.allInstrs (fun i => !Taint.clobbers i .rsp) = true
  depth : c.depth ≤ 1
  spSafe : c.all (fun i => !isa.writesSp i) = true

theorem eq_call (hq : EqCode (VG.Impl.Ed25519.X86_64.verifyEquation fld dbl)) (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : EqArgs L t)
    {challenge : List Byte} (hh : Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 64 = challenge) :
    WP isa (.call ("vg_ed25519_verify_equation" ++ fs) (verifyEquation fld dbl)) t fun t' => Ctx L g mx m₀ t' ∧
      t'.gpr .rax = Proof.Ed25519.X86_64.signWord (Spec.Ed25519.verifyEquation
        (Spec.Ed25519.bytesAt m₀ L.pk 32) (Spec.Ed25519.bytesAt m₀ L.sig 64) challenge) := by
  refine call_ok hL (verify_ok hq.mx) (Proof.Pbkdf2.Md.X86_64.nosp_of hq.noSp)
    hq.depth hc (eq_pre hL hc ha) ?_ ?_
    fun s' hc' _ _ ⟨s₂, _, hg, hpost⟩ => ⟨hc', ?_⟩
  · intro r hr
    simp only [eqRd, eqWr, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩
    · exact ⟨L.FR, by simp, within_base _ (by omega)⟩
    · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩
  · intro r hr
    simp only [eqWr, List.mem_singleton] at hr
    subst hr
    exact .inr (within_base _ (by omega))
  · obtain ⟨hdi, hsi, hdx, -⟩ := eq_regs ha (eqRd L) (eqWr L)
    change s₂.gpr .rax = Proof.Ed25519.X86_64.signWord (Spec.Ed25519.verifyEquation _ _ _) at hpost
    rw [hg .rax (by decide), hdi, hsi, hdx, State.withRegions_mem] at hpost
    have hpk := hc.ce_bytes hL (r := L.PK)
      ⟨L.PK, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 32 ≤ 2 ^ 64)
    have hsig := hc.ce_bytes hL (r := L.SIG)
      ⟨L.SIG, by simp [Lay.inputs], within_base _ (by omega)⟩ (by decide : 64 ≤ 2 ^ 64)
    have he : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 64 =
        Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 64 := by
      apply List.map_congr_left
      intro i hi
      exact PublicKey.ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 64⟩) (i := i)
        (by rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
        (by decide : 64 ≤ 2 ^ 64) (List.mem_range.mp hi)
    change Spec.Ed25519.bytesAt _ L.pk 32 = _ at hpk
    change Spec.Ed25519.bytesAt _ L.sig 64 = _ at hsig
    rw [hpk, hsig, he, hh] at hpost
    exact hpost

end VG.Proof.Ed25519.X86_64.VerifyMessage
