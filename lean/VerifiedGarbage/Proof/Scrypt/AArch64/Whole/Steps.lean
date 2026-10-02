import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Layout
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-!
# scrypt on AArch64: the blocks between the calls

The parameters as numbers (`Lay.Ok`), the frames' entry (`entry_ok`), and what
each block between the calls does: it keeps `Ctx`, and sets up the next call's
arguments (`PbkArgs`, `RomixArgs`) or the next block.
-/

namespace VG.Proof.Scrypt.AArch64.Whole

open VG VG.AArch64 VG.Impl.Scrypt.AArch64
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)

/-! ## Arithmetic -/

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem lsl7 (x : BitVec 64) : x <<< 7 = BitVec.ofNat 64 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

/-- `b` is not the whole address space, since the stack is not in it. -/
theorem blen_lt : L.blen.toNat * 128 < 2 ^ 64 :=
  toNat_le_of_disjoint h.kb.symm (by show (0 : Nat) < 96; omega)

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 64 := by have := h.blen_lt; have := h.r_le; omega

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

/-! ## In the frames -/

theorem add_add (p : Addr) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem read8 (m : Mem) (a : Addr) : m.read a 8 = m.readW a 64 := by
  simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]

namespace Ctx

variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem} {t t' : State}
  (hc : Ctx L g vv m₀ t)
include hc

theorem inFr {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 80) : InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inFrW {d : Nat} (h₁ : 16 ≤ d) (h₂ : d + 8 ≤ 80) : InRegions t.wr (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩

theorem inArgs (hL : L.Ok) {d : Nat} (h₁ : 96 ≤ d) (h₂ : d + 8 ≤ 136) :
    InRegions (t.rd ++ t.wr) (L.B + BitVec.ofNat 64 d) 8 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

/-- Code that writes only registers other than the callee-saved ones and
the vector registers. -/
theorem regs (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r) : Ctx L g vv m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'),
    fun r hr => by rw [hv]; exact hc.vs r hr, by rw [hm]; exact hc.kept, by rw [hm]; exact hc.frame⟩

/-- Code that also writes the frame's first word. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr) (hsp : t'.sp = t.sp)
    (hv : t'.v = t.v) (hg : ∀ r ∈ preserved, r ≠ .x30 → t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem) : Ctx L g vv m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp,
    fun r hr hr' => (hg r hr hr').trans (hc.cs r hr hr'), fun r hr => by rw [hv]; exact hc.vs r hr,
    hc.kept.frame hf fun d hd R hR => ?_, hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

/-- The registers a block writes, other than the callee-saved ones. -/
macro "scrypt_cs_tac" : tactic => `(tactic| (
  intro r hr _
  revert hr
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false]
  rintro (h | h | h | h | h | h | h | h | h | h | h) <;> subst h <;>
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_false]))

/-! ## The blocks -/

section
variable {L : Lay} {g : Reg → BitVec 64} {vv : VReg → BitVec 128} {m₀ : Mem}

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, `c = 1` and `scratch`. -/
structure PbkArgs (L : Lay) (salt : Addr) (sl : BitVec 64) (out : Addr) (ol : BitVec 64) (t : State) :
    Prop where
  x0 : t.gpr .x0 = L.pw
  x1 : t.gpr .x1 = L.pwl
  x2 : t.gpr .x2 = salt
  x3 : t.gpr .x3 = sl
  x4 : t.gpr .x4 = 1
  x5 : t.gpr .x5 = out
  x6 : t.gpr .x6 = ol
  x7 : t.gpr .x7 = L.scr

/-- The registers on entry to the frame's body, once our arguments are saved. -/
structure Entry (L : Lay) (t : State) : Prop where
  x0 : t.gpr .x0 = L.pw
  x1 : t.gpr .x1 = L.pwl
  x2 : t.gpr .x2 = L.salt
  x3 : t.gpr .x3 = L.sl
  x5 : t.gpr .x5 = L.b
  x6 : t.gpr .x6 = L.blen

theorem pbk1Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) (he : Entry L t) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g vv m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) t' := by
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pbk1Args, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, add_add,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, l104, read8, hc.kept.scr,
    Option.some.injEq, exists_eq_left', BitVec.shiftLeft_zero]
  refine ⟨hc.regs rfl rfl rfl rfl rfl (by scrypt_cs_tac), trivial, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, rfl⟩
  all_goals simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq]
  exacts [he.x0, he.x1, he.x2, he.x3, he.x5, by rw [he.x6, lsl7 _]]

/-- A 64-bit `write` is a `writeW`. -/
theorem write8 (m : Mem) (a : Addr) (v : BitVec 64) : m.write a 8 v = m.writeW a v := by
  simp only [Mem.writeW, Nat.reduceDiv, Nat.reduceMul, BitVec.setWidth_eq]

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) :
    WP isa (.block cur0) t fun t' => Ctx L g vv m₀ t' ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = L.b ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have w16 := hc.inFrW (d := 16) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [cur0, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT,
    and_self, l48, w16, read8, hc.kept.b, write8, Option.some.injEq, exists_eq_left']
  have f : Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem (t.mem.writeW (L.B + BitVec.ofNat 64 16) L.b) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.store hL rfl rfl hc.sp.symm rfl (by scrypt_cs_tac) f, Mem.readW_writeW_self64 _ _ _, f⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : Addr) (t : State) : Prop where
  x0 : t.gpr .x0 = cur
  x1 : t.gpr .x1 = L.r
  x2 : t.gpr .x2 = L.v
  x3 : t.gpr .x3 = L.vlen
  x4 : t.gpr .x4 = L.scr
  x5 : t.gpr .x5 = L.r + BitVec.ofNat 64 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = cur) :
    WP isa (.block romixArgs) t fun t' => Ctx L g vv m₀ t' ∧ t'.mem = t.mem ∧ RomixArgs L cur t' := by
  have l16 := hc.inFr (d := 16) (by omega) (by omega)
  have l40 := hc.inFr (d := 40) (by omega) (by omega)
  have l64 := hc.inFr (d := 64) (by omega) (by omega)
  have l96 := hc.inArgs hL (d := 96) (by omega) (by omega)
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [romixArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, add_add,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, l16, l40, l64, l96, l104,
    read8, hcur, hc.kept.r, hc.kept.v, hc.kept.vlen, hc.kept.scr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by scrypt_cs_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) {cur : Addr}
    (hcur : t.mem.readW (L.B + BitVec.ofNat 64 16) 64 = cur) :
    WP isa (.block nextBlock) t fun t' => Ctx L g vv m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem t'.mem ∧
      t'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = cur + BitVec.ofNat 64 (L.r.toNat * 128) ∧
      t'.gpr .x11 = L.b + BitVec.ofNat 64 (L.blen.toNat * 128) - (cur + BitVec.ofNat 64 (L.r.toNat * 128)) := by
  have l16 := hc.inFr (d := 16) (by omega) (by omega)
  have w16 := hc.inFrW (d := 16) (by omega) (by omega)
  have l40 := hc.inFr (d := 40) (by omega) (by omega)
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l56 := hc.inFr (d := 56) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [nextBlock, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.load, State.store,
    State.read, Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.sp_write, RegUpd.mem_write, Option.map_some, Option.bind_some, reduceCtorEq,
    ite_false, ite_true, hc.sp, add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT,
    and_self, l16, w16, l40, l48, l56, read8, hcur, hc.kept.r, hc.kept.b, hc.kept.blen, write8, lsl7,
    Option.some.injEq, exists_eq_left']
  have f : Frame [⟨L.B + BitVec.ofNat 64 16, 8⟩] t.mem
      (t.mem.writeW (L.B + BitVec.ofNat 64 16) (cur + BitVec.ofNat 64 (L.r.toNat * 128))) :=
    (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
  exact ⟨hc.store hL rfl rfl hc.sp.symm rfl (by scrypt_cs_tac) f, f, Mem.readW_writeW_self64 _ _ _, trivial⟩

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g vv m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g vv m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.b (BitVec.ofNat 64 (L.blen.toNat * 128)) L.out L.ol t' := by
  have l24 := hc.inFr (d := 24) (by omega) (by omega)
  have l32 := hc.inFr (d := 32) (by omega) (by omega)
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l56 := hc.inFr (d := 56) (by omega) (by omega)
  have l104 := hc.inArgs hL (d := 104) (by omega) (by omega)
  have l120 := hc.inArgs hL (d := 120) (by omega) (by omega)
  have l128 := hc.inArgs hL (d := 128) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pbk2Args, runBlock_cons, runStep_some, runBlock_nil, exec, State.load, State.read,
    Size.bits, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write, RegUpd.sp_write,
    RegUpd.mem_write, Option.map_some, reduceCtorEq, ite_false, ite_true, hc.sp, add_add,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, l24, l32, l48, l56, l104, l120,
    l128, read8, hc.kept.pw, hc.kept.pwl, hc.kept.b, hc.kept.blen, hc.kept.scr, hc.kept.out, hc.kept.ol,
    lsl7, BitVec.shiftLeft_zero, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl rfl (by scrypt_cs_tac), trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩

/-! ## Entering the frames -/

/-- Six words stored in the frame. -/
theorem six_ok (B : Addr) (m : Mem) (a b c d e f : BitVec 64) :
    let m' := (((((m.writeW (B + BitVec.ofNat 64 24) a).writeW (B + BitVec.ofNat 64 32) b).writeW
      (B + BitVec.ofNat 64 40) c).writeW (B + BitVec.ofNat 64 48) d).writeW (B + BitVec.ofNat 64 56) e).writeW
      (B + BitVec.ofNat 64 64) f
    Frame [⟨B + BitVec.ofNat 64 24, 48⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 24) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 32) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 40) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 48) 64 = d ∧ m'.readW (B + BitVec.ofNat 64 56) 64 = e ∧
      m'.readW (B + BitVec.ofNat 64 64) 64 = f := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 136 → y + 8 ≤ 136 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 24 ≤ x → x + 8 ≤ 72 →
      (⟨B + BitVec.ofNat 64 24, 48⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨((((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 24 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 32 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 40 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 48 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 56 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 64 (by omega) (by omega)), ?_, ?_, ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 24 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 48 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 32 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 32 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 32 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 32 48 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 32 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 40 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 40 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 40 48 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 48 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 48 56 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 56 64 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]

/-- The state in which the inner frame's body starts. -/
def entered (s : State) : State := allocated 64 (pushed .x30 s)

@[simp] theorem entered_rd (s : State) : (entered s).rd = s.rd := rfl
@[simp] theorem entered_gpr (s : State) : (entered s).gpr = s.gpr := rfl
@[simp] theorem entered_v (s : State) : (entered s).v = s.v := rfl

theorem entered_sp (s : State) : (entered s).sp = (lay s).B + BitVec.ofNat 64 16 := by
  show s.sp - 16 - BitVec.ofNat 64 64 = s.sp - BitVec.ofNat 64 96 + BitVec.ofNat 64 16
  bv_omega

theorem lr_slot (s : State) : s.sp - 16 = (lay s).B + BitVec.ofNat 64 80 := by
  show s.sp - 16 = s.sp - BitVec.ofNat 64 96 + BitVec.ofNat 64 80
  bv_omega

theorem entered_wr (s : State) :
    (entered s).wr = (lay s).FR :: (lay s).LR :: s.wr := by
  show (⟨s.sp - 16 - BitVec.ofNat 64 64, 64⟩ : Region) :: ⟨s.sp - 16, 16⟩ :: s.wr = _
  rw [show s.sp - 16 - BitVec.ofNat 64 64 = (lay s).B + BitVec.ofNat 64 16 from entered_sp s, lr_slot]

theorem entered_mem (s : State) :
    (entered s).mem = s.mem.writeW ((lay s).B + BitVec.ofNat 64 80) (s.gpr .x30) := by
  show s.mem.write (s.sp - 16) 8 (s.gpr .x30) = _
  rw [lr_slot, write8]

theorem arg_slot (s : State) (i : Nat) (hi : i < 5) :
    stackArgAddr s i = (lay s).B + BitVec.ofNat 64 (96 + 8 * i) := by
  simp only [stackArgAddr, lay]
  have : 8 * i < 2 ^ 64 := by omega
  bv_omega

theorem entry_ok {s : State} (h : Proof.Scrypt.scryptAArch64.pre s) :
    WP isa (.block saveArgs) (entered s) fun t => Ctx (lay s) s.gpr s.v s.mem t ∧ Entry (lay s) t := by
  have hL := lay_ok h
  have hnB := hL.nB
  have hw : ∀ d, 16 ≤ d → d + 8 ≤ 80 → InRegions (entered s).wr ((lay s).B + BitVec.ofNat 64 d) 8 :=
    fun d h₁ h₂ => ⟨(lay s).FR, by rw [entered_wr]; simp, Offset.contains _ h₁ (by omega) (by omega)⟩
  have w24 := hw 24 (by omega) (by omega)
  have w32 := hw 32 (by omega) (by omega)
  have w40 := hw 40 (by omega) (by omega)
  have w48 := hw 48 (by omega) (by omega)
  have w56 := hw 56 (by omega) (by omega)
  have w64 := hw 64 (by omega) (by omega)
  apply WP.of_runBlock
  simp only [saveArgs, runBlock_cons, runStep_some, runBlock_nil, exec, addr, State.store, State.read,
    Size.bits, Size.bytes, BitVec.setWidth_eq, RegUpd.gpr_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.sp_write, RegUpd.mem_write, Option.bind_some, reduceCtorEq, ite_false, ite_true, entered_sp,
    add_add, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod, Nat.reduceLT, and_self, w24, w32, w40, w48, w56,
    w64, write8, Option.some.injEq, exists_eq_left', BitVec.add_zero, entered_gpr]
  obtain ⟨f, k24, k32, k40, k48, k56, k64⟩ := six_ok (lay s).B (entered s).mem (s.gpr .x0) (s.gpr .x1)
    (s.gpr .x4) (s.gpr .x5) (s.gpr .x6) (s.gpr .x7)
  rw [entered_mem] at f k24 k32 k40 k48 k56 k64
  have keepF : ∀ d, ((lay s).B.toNat + d + 8 ≤ 2 ^ 64) → (72 ≤ d) →
      Region.Disjoint ⟨(lay s).B + BitVec.ofNat 64 d, 8⟩ ⟨(lay s).B + BitVec.ofNat 64 24, 48⟩ :=
    fun d h₁ h₂ => Offset.disjoint _ (by omega) (by omega) (by omega)
  have lr : ∀ m : Mem, Frame [⟨(lay s).B + BitVec.ofNat 64 24, 48⟩]
      (s.mem.writeW ((lay s).B + BitVec.ofNat 64 80) (s.gpr .x30)) m →
      m.readW ((lay s).B + BitVec.ofNat 64 80) 64 = s.gpr .x30 := fun m hf => by
    rw [hf.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact keepF 80 (by omega) (by omega)) (by decide)]
    exact Mem.readW_writeW_self64 _ _ _
  have arg : ∀ i, i < 5 → ∀ m : Mem, Frame [⟨(lay s).B + BitVec.ofNat 64 24, 48⟩]
      (s.mem.writeW ((lay s).B + BitVec.ofNat 64 80) (s.gpr .x30)) m →
      m.readW ((lay s).B + BitVec.ofNat 64 (96 + 8 * i)) 64 = stackArg s i := fun i hi m hf => by
    rw [hf.readW (Region.contains_self _ _) (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact keepF _ (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), stackArg,
      arg_slot s i hi]
  rw [entered_mem]
  refine ⟨⟨?_, ?_, rfl, ?_, fun _ _ => by simp only [RegUpd.v_write, entered_v], ⟨k24, k32, k40, k48, k56, k64, lr _ f, arg 0 (by omega) _ f,
    arg 1 (by omega) _ f, arg 3 (by omega) _ f, arg 4 (by omega) _ f⟩, ?_⟩, ?_⟩
  · simp only [entered_rd]
    rw [h.2.2.1, ← lay_args]; rfl
  · rw [entered_wr, h.2.2.2.1]; rfl
  · intro r hr hr'
    rw [RegUpd.gpr_write_of_ne _ _ _ (by
      intro e; subst e; simp [preserved] at hr), entered_gpr]
  · refine Frame.trans (Frame.writeW (Frame.refl _ _) (r := (lay s).STK) (by simp) _
      (Offset.contains_base _ (by omega) (by omega))) (Frame.sub f fun r hr => ?_)
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨(lay s).STK, by simp, Offset.sub_base _ (by omega)⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [RegUpd.gpr_write, reduceCtorEq, ite_false, entered_gpr] <;> rfl

end

end VG.Proof.Scrypt.AArch64.Whole
