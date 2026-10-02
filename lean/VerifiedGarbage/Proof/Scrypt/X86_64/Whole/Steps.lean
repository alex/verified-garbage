import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Layout
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# scrypt on x86-64: the blocks between the calls

Untrusted: everything here is checked by Lean. The parameters as numbers
(`Lay.Ok`), and what each block between the calls does: it keeps `Ctx`, and
sets up the next call's arguments (`PbkArgs`, `RomixArgs`) or the next block.
-/

namespace VG.Proof.Scrypt.X86_64.Whole

open VG VG.X86_64 VG.Impl.Scrypt.X86_64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt)

/-! ## Arithmetic -/

/-- Rotating right by 57 multiplies by 128 a number less than `2^57`. -/
theorem ror57 (x : BitVec 64) (h : x.toNat < 2 ^ 57) :
    x.rotateRight 57 = BitVec.ofNat 64 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show 57 % 64 = 57 from rfl, Nat.div_eq_of_lt h, Nat.zero_or]

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem vlen_eq : L.vlen.toNat = L.r.toNat * L.NN := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.vmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1
theorem NN_pos : 0 < L.NN := by have := h.valid.1; omega

/-- `b` is not the whole address space, since the stack is not in it. -/
theorem blen_lt : L.blen.toNat * 128 < 2 ^ 64 :=
  toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 88; omega)
theorem vlen_lt : L.vlen.toNat * 128 < 2 ^ 64 :=
  toNat_le_of_disjoint h.kv.symm (by show (0 : Nat) < 88; omega)

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem blen57 : L.blen.toNat < 2 ^ 57 := by have := h.blen_lt; omega
theorem r57 : L.r.toNat < 2 ^ 57 := by have := h.blen57; have := h.r_le; omega

/-- `128 r p`, the length of `b`. -/
theorem len_b : 128 * L.r.toNat * L.pp = L.blen.toNat * 128 := by
  rw [h.blen_eq, Nat.mul_comm 128, Nat.mul_assoc, Nat.mul_comm 128, Nat.mul_assoc]

/-- The derived key of step 1 is not too long for PBKDF2. -/
theorem ol1 : L.blen.toNat * 128 ≤ (2 ^ 32 - 1) * 32 := by
  have h₁ := h.valid.2.2.2.2.1
  have h₂ := Nat.div_mul_le_self ((2 ^ 32 - 1) * 32) (128 * L.r.toNat)
  have h₃ : L.pp * (128 * L.r.toNat) ≤ (2 ^ 32 - 1) * 32 / (128 * L.r.toNat) * (128 * L.r.toNat) :=
    Nat.mul_le_mul_right _ h₁
  rw [← h.len_b, Nat.mul_comm (128 * L.r.toNat)]
  omega

theorem slen17 : 17 ≤ L.slen.toNat := by have := h.slen; have := h.rpos; omega

end Lay.Ok

/-! ## In the frame -/

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

theorem ea_sp (t : State) (d : Nat) : t.ea (sp d) = t.gpr .rsp + BitVec.ofNat 64 d := by
  show t.gpr .rsp + BitVec.ofInt 64 (d : Int) = _
  rw [ofInt_nat]

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem cs_keep {t : State} {d : Reg} (v : BitVec 64) (hd : d ∉ calleeSaved) :
    ∀ r ∈ calleeSaved, (t.setReg d v).gpr r = t.gpr r :=
  fun _ hr => RegUpd.gpr_setReg_of_ne _ _ (fun e => hd (e ▸ hr))

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem} {t t' : State} (hc : Ctx L g m₀ t)
include hc

theorem inFr {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 88) : InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW {d : Nat} (h₁ : 32 ≤ d) (h₂ : d + 8 ≤ 88) : InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inArgs (hL : L.Ok) {d : Nat} (h₁ : 96 ≤ d) (h₂ : d + 8 ≤ 152) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

/-- Code that writes only caller-saved registers. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hm : t'.mem = t.mem)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hm]; exact hc.kept,
    by rw [hm]; exact hc.frame⟩

/-- Code that writes only caller-saved registers and the frame's first three words. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem) : Ctx L g m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun d hd R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

/-- The registers the frame's body may write, and that `scrypt_cs_tac` steps through. -/
macro "scrypt_cs_tac" : tactic => `(tactic| (
  intro r hr
  revert hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))


/-! ## The blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, `c = 1`, and on the stack `ol`
and `scratch`. -/
structure PbkArgs (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  rdi : t.gpr .rdi = L.pw
  rsi : t.gpr .rsi = L.pwl
  rdx : t.gpr .rdx = salt
  rcx : t.gpr .rcx = sl
  r8 : t.gpr .r8 = (1 : BitVec 32).setWidth 64
  r9 : t.gpr .r9 = out
  a0 : t.mem.readW (L.B + BitVec.ofNat 64 32) 64 = ol
  a1 : t.mem.readW (L.B + BitVec.ofNat 64 40) 64 = L.scr

/-- The registers on entry to the frame's body. -/
structure Entry (L : Lay) (t : State) : Prop where
  rdi : t.gpr .rdi = L.pw
  rsi : t.gpr .rsi = L.pwl
  rdx : t.gpr .rdx = L.salt
  rcx : t.gpr .rcx = L.sl
  r9 : t.gpr .r9 = L.b

theorem w32 (B : Addr) (m : Mem) (a c : BitVec 64) :
    let m' := (m.writeW (B + BitVec.ofNat 64 32) a).writeW (B + BitVec.ofNat 64 40) c
    Frame [⟨B + BitVec.ofNat 64 32, 24⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 32) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 40) 64 = c := by
  refine ⟨((Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (Offset.contains _ (by omega) (by omega) (by omega)), ?_, Mem.readW_writeW_self64 _ _ _⟩
  rw [Mem.readW_writeW_sep (Offset.sep B (by omega) (by omega) (by omega)) (by decide),
    Mem.readW_writeW_self64]

theorem pbk1Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (he : Entry L t) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g m₀ t' ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem := by
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  have w32' := hc.inFrW (d := 32) (by omega) (by omega)
  have w40 := hc.inFrW (d := 40) (by omega) (by omega)
  have r := ror57 _ (hL.blen57)
  apply WP.of_runBlock
  simp only [pbk1Args, times128, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc,
    readSrc32, State.load64, State.store64, State.setReg32, ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.mem_setFlags, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, l96, l120, w32', w40, hc.kept.blen, hc.kept.scr, r, Option.some.injEq,
    exists_eq_left', show (1 ≤ 57 ∧ 57 ≤ 63) = True from by decide]
  obtain ⟨f, a0, a1⟩ := w32 L.B t.mem (BitVec.ofNat 64 (L.blen.toNat * 128)) L.scr
  refine ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, ⟨?_, ?_, ?_, ?_, rfl, ?_, a0, a1⟩, f⟩
  all_goals simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, ite_false]
  exacts [he.rdi, he.rsi, he.rdx, he.rcx, he.r9]

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block cur0) t fun t' => Ctx L g m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = L.b ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem := by
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have w48 := hc.inFrW (d := 48) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [cur0, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    State.store64, ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, l80, w48,
    hc.kept.b, Option.some.injEq, exists_eq_left']
  have f : Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 48) L.b) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  exact ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, Mem.readW_writeW_self64 _ _ _, f⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : Addr) (t : State) : Prop where
  rdi : t.gpr .rdi = cur
  rsi : t.gpr .rsi = L.r
  rdx : t.gpr .rdx = L.v
  rcx : t.gpr .rcx = L.vlen
  r8 : t.gpr .r8 = L.scr
  r9 : t.gpr .r9 = L.r + (2 : BitVec 32).signExtend 64

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ RomixArgs L cur t' := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l72 := hc.inFr (d := 72) (by omega) (by omega)
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  have l112 := hc.inArgs hL (d := 112) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [romixArgs, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    State.load64, ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags,
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, l48, l72, l104, l112, l120, hcur, hc.kept.r, hc.kept.v, hc.kept.vlen,
    hc.kept.scr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl (by scrypt_cs_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 48) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 48) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.zf = some (cur + BitVec.ofNat 64 (L.r.toNat * 128) -
        (BitVec.ofNat 64 (L.blen.toNat * 128) + L.b) == 0) := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have w48 := hc.inFrW (d := 48) (by omega) (by omega)
  have l72 := hc.inFr (d := 72) (by omega) (by omega)
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have r₁ := ror57 _ (hL.r57)
  have r₂ := ror57 _ (hL.blen57)
  apply WP.of_runBlock
  simp only [nextBlock, times128, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execShift,
    readSrc, State.load64, State.store64, ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags, RegUpd.mem_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.zf_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hc.rsp,
    add_add, Nat.reduceAdd, l48, w48, l72, l80, l96, hcur, hc.kept.r, hc.kept.blen, hc.kept.b, r₁, r₂,
    Option.some.injEq, exists_eq_left', show (1 ≤ 57 ∧ 57 ≤ 63) = True from by decide]
  have f : Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem
      (t.mem.writeW (L.B + BitVec.ofNat 64 48) (cur + BitVec.ofNat 64 (L.r.toNat * 128))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega) (by omega))
  exact ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, f, Mem.readW_writeW_self64 _ _ _, trivial⟩

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g m₀ t' ∧
      PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 32, 24⟩] t.mem t'.mem := by
  have l56 := hc.inFr (d := 56) (by omega) (by omega)
  have l64 := hc.inFr (d := 64) (by omega) (by omega)
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  have l136 := hc.inArgs hL (d := 136) (by omega) (by omega)
  have l144 := hc.inArgs hL (d := 144) (by omega) (by omega)
  have w32' := hc.inFrW (d := 32) (by omega) (by omega)
  have w40 := hc.inFrW (d := 40) (by omega) (by omega)
  have r := ror57 _ (hL.blen57)
  apply WP.of_runBlock
  simp only [pbk2Args, times128, runBlock_cons, runStep_some, runBlock_nil, exec, execShift, readSrc,
    readSrc32, State.load64, State.store64, State.setReg32, ea_sp, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setFlags, RegUpd.rd_setFlags, RegUpd.wr_setFlags,
    RegUpd.mem_setFlags, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add,
    Nat.reduceAdd, l56, l64, l80, l96, l120, l136, l144, w32', w40, hc.kept.pw, hc.kept.pwl, hc.kept.b,
    hc.kept.blen, hc.kept.scr, hc.kept.out, hc.kept.ol, r, Option.some.injEq, exists_eq_left',
    show (1 ≤ 57 ∧ 57 ≤ 63) = True from by decide]
  obtain ⟨f, a0, a1⟩ := w32 L.B t.mem L.ol L.scr
  refine ⟨hc.store hL rfl rfl (by scrypt_cs_tac) f, ⟨?_, ?_, ?_, ?_, rfl, ?_, a0, a1⟩, f⟩
  all_goals simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, reduceCtorEq, ite_false, ite_true]

end

end VG.Proof.Scrypt.X86_64.Whole
