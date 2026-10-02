import VerifiedGarbage.Proof.Rc2.Arm.Stream.Common
import VerifiedGarbage.Proof.Rc2.PairMem

/-! # Streaming RC2-CBC on ARMv7: `vg_rc2_cbc_init`

Untrusted: everything here is checked by Lean. The checks of the lengths
(`checks_ok`), then, if they pass, the IV copied to `ctx + 128` and `lr`
saved (`args_ok`), the call of `vg_rc2_expand_key` (`key_call`), and `lr`
restored with 0 returned (`tail_ok`). -/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Arm.RegUpd VG.Impl.Rc2.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg op2_lsr wp_mov wp_sub wp_cmp wp_ldr wp_str
  wp_ldrSp eval_ne sub_beq)

theorem range7 (x : BitVec 32) :
    ((x - 1) >>> 7 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 128) := by
  rw [show ((x - 1) >>> 7 - 0 : BitVec 32) = (x - 1) >>> 7 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 7).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 128 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega

theorem range10 (x : BitVec 32) :
    ((x - 1) >>> 10 - 0 == 0) = decide (1 ≤ x.toNat ∧ x.toNat ≤ 1024) := by
  rw [show ((x - 1) >>> 10 - 0 : BitVec 32) = (x - 1) >>> 10 from BitVec.sub_zero _]
  have e : ((x - 1) >>> 10).toNat = (2 ^ 32 - 1 + x.toNat) % 2 ^ 32 / 1024 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]; rfl
  have h := x.isLt
  apply Bool.eq_iff_iff.mpr
  rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, e, show (0 : BitVec 32).toNat = 0 from rfl]
  omega

theorem eq8 (x : BitVec 32) : (x - 8 == 0) = decide (x.toNat = 8) := by
  rw [ofNat_toNat32 x, show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, sub_beq x.isLt (by decide),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem setWidth_append (a b : BitVec 32) : BitVec.setWidth 32 (a ++ b) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append]
  have := b.isLt
  rw [Nat.shiftLeft_eq, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt this]
  omega

theorem wp_mov_imm {is : List Instr} {s : State} {Q : State → Prop} {d : Reg} {v : BitVec 32}
    (he : encodable v = true) (k : WP isa (.block is) (s.setReg d v) Q) :
    WP isa (.block (.mov d (.imm v) :: is)) s Q :=
  VG.Proof.MdStream.Arm.WP.cons (by simp [exec, Op2.eval, he]) k

/-- The lengths are valid. -/
abbrev IValid (s : State) : Prop :=
  (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) ∧ (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) ∧
    (stackArg s 0).toNat = 8

/-- The error code for invalid lengths. -/
abbrev ICode (s : State) : Nat :=
  if ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) then 1
  else if ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) then 2 else 3

/-- What the checks leave. -/
structure CheckPost (s c : State) : Prop where
  keep : ∀ r, r ≠ .r0 → r ≠ .r12 → c.gpr r = s.gpr r
  mem : c.mem = s.mem
  rd : c.rd = s.rd
  wr : c.wr = s.wr
  sp : c.sp = s.sp
  z : c.z = decide (IValid s)
  ok : IValid s → c.gpr .r0 = s.gpr .r0
  err : ¬ IValid s → (c.gpr .r0).toNat = ICode s

theorem checks_ok (s : State) (hs : initContract.pre s) : WP isa checks s (CheckPost s) := by
  obtain ⟨_, spfit, hrd, _⟩ := hs
  rw [checks]
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₁ u₁ => wp_mov (op2_lsr (by decide)) fun c₂ u₂ =>
    wp_cmp (op2_imm (by decide)) fun c₃ f₃ z₃ => WP.block_nil ?_)
  have hk : c₃.z = decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := by
    rw [z₃, u₂.gpr, u₁.gpr, range7]
  have g₃ (r : Reg) (h : r ≠ .r12) : c₃.gpr r = s.gpr r := by rw [f₃.gpr, u₂.other _ h, u₁.other _ h]
  have mem₃ : c₃.mem = s.mem := by rw [f₃.mem, u₂.mem, u₁.mem]
  have rd₃ : c₃.rd = s.rd := by rw [f₃.rd, u₂.rd, u₁.rd]
  have wr₃ : c₃.wr = s.wr := by rw [f₃.wr, u₂.wr, u₁.wr]
  have sp₃ : c₃.sp = s.sp := by rw [f₃.sp, u₂.sp, u₁.sp]
  refine WP.ite (!decide (1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128))
    (by show eval .ne c₃ = _; rw [eval_ne, hk]) (fun hb => wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb => ?_
  · have hb : ¬(1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128) := fun h => by simp [h] at hb
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₃ r h12], by rw [mem_setReg, mem₃],
      by rw [rd_setReg, rd₃], by rw [wr_setReg, wr₃], by rw [sp_setReg, sp₃], ?_, fun h => absurd h.1 hb,
      fun _ => ?_⟩
    · rw [z_setReg, hk]; simp only [IValid, hb, false_and, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, not_false_eq_true, ite_true]; rfl
  have hb : 1 ≤ (s.gpr .r1).toNat ∧ (s.gpr .r1).toNat ≤ 128 := by simpa using hb
  refine WP.seq (wp_sub (op2_imm (by decide)) fun c₄ u₄ => wp_mov (op2_lsr (by decide)) fun c₅ u₅ =>
    wp_cmp (op2_imm (by decide)) fun c₆ f₆ z₆ => WP.block_nil ?_)
  have he : c₆.z = decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := by
    rw [z₆, u₅.gpr, u₄.gpr, g₃ _ (by decide), range10]
  have g₆ (r : Reg) (h : r ≠ .r12) : c₆.gpr r = s.gpr r := by rw [f₆.gpr, u₅.other _ h, u₄.other _ h, g₃ r h]
  have mem₆ : c₆.mem = s.mem := by rw [f₆.mem, u₅.mem, u₄.mem, mem₃]
  have rd₆ : c₆.rd = s.rd := by rw [f₆.rd, u₅.rd, u₄.rd, rd₃]
  have wr₆ : c₆.wr = s.wr := by rw [f₆.wr, u₅.wr, u₄.wr, wr₃]
  have sp₆ : c₆.sp = s.sp := by rw [f₆.sp, u₅.sp, u₄.sp, sp₃]
  refine WP.ite (!decide (1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024))
    (by show eval .ne c₆ = _; rw [eval_ne, he]) (fun hb' => wp_mov_imm (by decide) (WP.block_nil ?_)) fun hb' => ?_
  · have hb' : ¬(1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024) := fun h => by simp [h] at hb'
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₆ r h12], by rw [mem_setReg, mem₆],
      by rw [rd_setReg, rd₆], by rw [wr_setReg, wr₆], by rw [sp_setReg, sp₆], ?_, fun h => absurd h.2.1 hb',
      fun _ => ?_⟩
    · rw [z_setReg, he]; simp only [IValid, hb', false_and, and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, hb', not_false_eq_true, ite_true]
      rfl
  have hb' : 1 ≤ (s.gpr .r2).toNat ∧ (s.gpr .r2).toNat ≤ 1024 := by simpa using hb'
  rw [show checkIv = [.ldrSp .r12 0, .cmp .r12 (.imm 8)] from rfl]
  refine WP.seq (wp_ldrSp (a := stackArgAddr s 0) (by decide) (by rw [sp₆]; rfl)
    (by rw [rd₆, wr₆]; exact argIn (by rw [hrd]; simp) (by decide) spfit) fun c₇ u₇ =>
      wp_cmp (op2_imm (by decide)) fun c₈ f₈ z₈ => WP.block_nil ?_)
  have hi : c₈.z = decide ((stackArg s 0).toNat = 8) := by
    rw [z₈, u₇.gpr, mem₆, eq8]; rfl
  have g₈ (r : Reg) (h : r ≠ .r12) : c₈.gpr r = s.gpr r := by rw [f₈.gpr, u₇.other _ h, g₆ r h]
  have mem₈ : c₈.mem = s.mem := by rw [f₈.mem, u₇.mem, mem₆]
  have rd₈ : c₈.rd = s.rd := by rw [f₈.rd, u₇.rd, rd₆]
  have wr₈ : c₈.wr = s.wr := by rw [f₈.wr, u₇.wr, wr₆]
  have sp₈ : c₈.sp = s.sp := by rw [f₈.sp, u₇.sp, sp₆]
  refine WP.ite (!decide ((stackArg s 0).toNat = 8))
    (by show eval .ne c₈ = _; rw [eval_ne, hi]) (fun hb'' => wp_mov_imm (by decide) (WP.block_nil ?_))
    fun hb'' => WP.block_nil ?_
  · have hb'' : ¬(stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r h0 h12 => by rw [gpr_setReg_of_ne _ _ h0, g₈ r h12], by rw [mem_setReg, mem₈],
      by rw [rd_setReg, rd₈], by rw [wr_setReg, wr₈], by rw [sp_setReg, sp₈], ?_, fun h => absurd h.2.2 hb'',
      fun _ => ?_⟩
    · rw [z_setReg, hi]; simp only [IValid, hb'', and_false, decide_false]
    · rw [gpr_setReg_self]; simp only [ICode, hb, hb']; rfl
  · have hb'' : (stackArg s 0).toNat = 8 := by simpa using hb''
    refine ⟨fun r _ h12 => g₈ r h12, mem₈, rd₈, wr₈, sp₈, ?_, fun _ => g₈ _ (by decide),
      fun h => absurd ⟨hb, hb', hb''⟩ h⟩
    rw [hi]; simp only [IValid, hb, hb', hb'', and_self, decide_true]

end VG.Proof.Rc2.Arm.Stream
