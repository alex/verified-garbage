import VerifiedGarbage.Proof.Scrypt.Arm.Whole.Layout

/-!
# scrypt on 32-bit ARM: the blocks between the calls

Untrusted: everything here is checked by Lean. The parameters as numbers
(`Lay.Ok`), the saving of our caller's registers (`save1_ok`, `save2_ok`,
`save3_ok`), and what each block between the calls does: it keeps `Ctx`,
and sets up the next call's arguments (`PbkArgs`, `RomixArgs`) or the next
block; `restore_ok` restores our caller's registers.
-/

namespace VG.Proof.Scrypt.Arm.Whole

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt toNat_add_ofNat)

/-! ## Arithmetic -/

theorem toNat_le_of_disjoint {R S : Region} (h : R.Disjoint S) (hS : 0 < S.len) : R.len < 2 ^ 64 := by
  refine Nat.lt_of_not_le fun hR => h S.base ?_ ?_
  · simp only [Region.Contains]; have := (S.base - R.base).isLt; omega
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega

theorem lsl7 (x : BitVec 32) : x <<< 7 = BitVec.ofNat 32 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

theorem blen_lt : L.blen.toNat * 128 < 2 ^ 32 := by
  have hnb := h.nb; have hS := h.nS; have hA := h.nA
  refine Nat.lt_of_not_le fun hge => ?_
  have hb0 : L.b.toNat = 0 := by omega
  have e : L.blen.toNat * 128 = 2 ^ 32 := by omega
  have eb : State.addr L.b = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_addr, hb0]; rfl
  have ex : (State.addr L.sp - BitVec.ofNat 64 40).toNat = L.sp.toNat - 40 := by
    rw [Offset.toNat_sub_ofNat, toNat_addr]; omega
  apply h.kb (State.addr L.sp - BitVec.ofNat 64 40)
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · have z : ∀ x : BitVec 64, x - State.addr L.b = x := fun x => by rw [eb]; exact BitVec.sub_zero x
    simp only [Region.Contains, z, e, ex]; omega

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r_lt : L.r.toNat * 128 < 2 ^ 32 := by have := h.blen_lt; have := h.r_le; omega

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

end Lay.Ok

/-! ## Words at offsets -/

/-- A word read back past a store of another at a different offset. -/
theorem rd_off {P : Addr} {m : Mem} {x y : Nat} {v : BitVec 32} (h : x + 4 ≤ y ∨ y + 4 ≤ x)
    (hx : x + 4 ≤ 64) (hy : y + 4 ≤ 64) :
    (m.writeW (P + BitVec.ofNat 64 y) v).readW (P + BitVec.ofNat 64 x) 32 =
      m.readW (P + BitVec.ofNat 64 x) 32 :=
  Mem.readW_writeW_sep (Offset.sep P h (by omega) (by omega)) (by decide)

theorem z32 : BitVec.ofNat 32 0 = 0 := rfl

theorem enc1 : encodable (1 : BitVec 32) = true := by decide
theorem enc2 : encodable (2 : BitVec 32) = true := by decide
theorem enc1920 : encodable (1920 : BitVec 32) = true := by decide

/-! ## Saving our caller's registers -/

/-- The state before the calls: our arguments, and our caller's `r0`–`r11`
(`g`) but `r12` and `lr`. -/
structure E (L : Lay) (g : Reg → BitVec 32) (m₀ : Mem) (t : State) : Prop where
  rd : t.rd = [L.PW, L.SALT, L.ARGS]
  wr : t.wr = [L.BB, L.VV, L.SC, L.OUT]
  sp : t.sp = L.sp
  regs : ∀ r, r ≠ .r12 → r ≠ .lr → t.gpr r = g r
  args : Args L t.mem
  frame : Frame [L.SC] m₀ t.mem
  g0 : g .r0 = L.pw
  g1 : g .r1 = L.pwl
  g2 : g .r2 = L.salt
  g3 : g .r3 = L.sl

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

theorem E.inArgs {t : State} (he : E L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 k)) 4 :=
  ⟨L.ARGS, by rw [he.rd, he.wr]; simp, by
    rw [he.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega)⟩

theorem E.inSc {t : State} (he : E L g m₀ t) {k : Nat} (hk : k + 4 ≤ L.slen.toNat * 128) :
    InRegions t.wr (State.addr L.scr + BitVec.ofNat 64 k) 4 :=
  ⟨L.SC, by rw [he.wr]; simp, Offset.contains_base _ hk (by omega)⟩

/-- The save area is apart from the first word of `scratch`, and from our stack arguments. -/
theorem sv_sc0 (hL : L.Ok) : L.SV.Disjoint ⟨State.addr L.scr, 4⟩ :=
  Offset.disjoint_base _ (by omega) (by have := hL.nc; have := hL.slen; omega)

/-- `E` after code that writes only `r12`, `lr` and `scratch`. -/
theorem E.upd {t t' : State} (he : E L g m₀ t) (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hg : ∀ r, r ≠ .r12 → r ≠ .lr → t'.gpr r = t.gpr r)
    (hf : Frame [L.SC] t.mem t'.mem) : E L g m₀ t' :=
  ⟨hrd.trans he.rd, hwr.trans he.wr, hsp.trans he.sp, fun r h₁ h₂ => (hg r h₁ h₂).trans (he.regs r h₁ h₂),
    he.args.frame hf (fun R hR => by
      simp only [List.mem_singleton] at hR; subst hR; exact hL.ca.symm),
    he.frame.trans hf, he.g0, he.g1, he.g2, he.g3⟩

/-- `save1`: our return address into the first word of `scratch`. -/
theorem save1_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (hlr : t.gpr .lr = g .lr) :
    WP isa (.block save1) t fun t' => E L g m₀ t' ∧ t'.gpr .lr = g .lr ∧ t'.gpr .r12 = L.scr ∧
      t'.mem.readW (State.addr L.scr) 32 = g .lr := by
  have l20 := he.inArgs hL (k := 20) (by omega)
  have w0 := he.inSc (k := 0) (by have := hL.slen17; omega)
  rw [BitVec.add_zero] at w0
  have a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.scr
  apply WP.of_runBlock
  simp only [save1, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Nat.reduceLT, ite_true, l20, a20, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, BitVec.add_zero, w0, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, reduceCtorEq, ite_false, hlr]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ _ => by simp only [RegUpd.gpr_setReg, h₁, ite_false]) ?_,
    trivial, trivial, Mem.readW_writeW_self32 _ _ _⟩
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := hL.slen17; omega)

/-- A word read back past a store into the save area, from outside it. -/
theorem rd_dis {a P : Addr} {m : Mem} {y : Nat} {v : BitVec 32} (hd : Region.Disjoint ⟨a, 4⟩ ⟨P, 36⟩)
    (hy : y + 4 ≤ 36) : (m.writeW (P + BitVec.ofNat 64 y) v).readW a 32 = m.readW a 32 :=
  Mem.readW_writeW_sep (Region.Disjoint.sep hd (Region.contains_self _ _)
    (Offset.contains_base _ hy (by omega))) (by decide)

/-- The first eight words of the save area. -/
structure Saved8 (L : Lay) (g : Reg → BitVec 32) (m : Mem) : Prop where
  r4 : m.readW (L.SVA + BitVec.ofNat 64 0) 32 = g .r4
  r5 : m.readW (L.SVA + BitVec.ofNat 64 4) 32 = g .r5
  r6 : m.readW (L.SVA + BitVec.ofNat 64 8) 32 = g .r6
  r7 : m.readW (L.SVA + BitVec.ofNat 64 12) 32 = g .r7
  r8 : m.readW (L.SVA + BitVec.ofNat 64 16) 32 = g .r8
  r9 : m.readW (L.SVA + BitVec.ofNat 64 20) 32 = g .r9
  r10 : m.readW (L.SVA + BitVec.ofNat 64 24) 32 = g .r10
  r11 : m.readW (L.SVA + BitVec.ofNat 64 28) 32 = g .r11

theorem sva_k (L : Lay) (k : Nat) :
    L.SVA + BitVec.ofNat 64 k = State.addr L.scr + BitVec.ofNat 64 (128 * (L.r.toNat + 15) + k) := by
  rw [Lay.SVA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem sv_con (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) : L.SC.Contains (L.SVA + BitVec.ofNat 64 k) 4 := by
  rw [sva_k]
  exact Offset.contains_base _ (by have := hL.slen; omega) (by have := hL.nc; have := hL.slen; omega)

theorem sv_in (hL : L.Ok) {t : State} (he : E L g m₀ t) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions t.wr (L.SVA + BitVec.ofNat 64 k) 4 :=
  ⟨L.SC, by rw [he.wr]; simp, sv_con hL hk⟩

/-- A store into the save area is within `scratch`. -/
theorem Frame.sv (hL : L.Ok) {m m' : Mem} (hf : Frame [L.SC] m m') {k : Nat} (hk : k + 4 ≤ 36)
    (v : BitVec 32) : Frame [L.SC] m (m'.writeW (L.SVA + BitVec.ofNat 64 k) v) :=
  hf.writeW (List.mem_singleton_self _) _ (sv_con hL hk)

/-- `save2`: our caller's `r4`–`r11` into the save area, whose address is
left in `r12`. -/
theorem save2_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (h12 : t.gpr .r12 = L.scr)
    (h0 : t.mem.readW (State.addr L.scr) 32 = g .lr) :
    WP isa (.block save2) t fun t' => E L g m₀ t' ∧ t'.gpr .r12 = L.svb ∧
      t'.mem.readW (State.addr L.scr) 32 = g .lr ∧ Saved8 L g t'.mem := by
  have l0 := he.inArgs hL (k := 0) (by omega)
  have a0 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 0)) 32 = L.r := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.r
  have s0 := hL.svb_addr (k := 0) (by omega)
  have s4 := hL.svb_addr (k := 4) (by omega)
  have s8 := hL.svb_addr (k := 8) (by omega)
  have s12 := hL.svb_addr (k := 12) (by omega)
  have s16 := hL.svb_addr (k := 16) (by omega)
  have s20 := hL.svb_addr (k := 20) (by omega)
  have s24 := hL.svb_addr (k := 24) (by omega)
  have s28 := hL.svb_addr (k := 28) (by omega)
  have w0 := sv_in hL he (k := 0) (by omega)
  have w4 := sv_in hL he (k := 4) (by omega)
  have w8 := sv_in hL he (k := 8) (by omega)
  have w12 := sv_in hL he (k := 12) (by omega)
  have w16 := sv_in hL he (k := 16) (by omega)
  have w20 := sv_in hL he (k := 20) (by omega)
  have w24 := sv_in hL he (k := 24) (by omega)
  have w28 := sv_in hL he (k := 28) (by omega)
  apply WP.of_runBlock
  simp only [save2, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Op2.eval, Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l0, a0, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, reduceCtorEq, ite_false, h12, enc1920, s0, s4, s8, s12, s16, s20,
    s24, s28, w0, w4, w8, w12, w16, w20, w24, w28]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₁, h₂, ite_false]) ?_,
    trivial, ?_, ?_⟩
  · repeat (first | exact Frame.refl _ _ | refine Frame.sv hL ?_ (by omega) _)
  · simp (disch := decide) only [rd_dis (sv_sc0 hL).symm]; exact h0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp (disch := decide) only [rd_off, Mem.readW_writeW_self32] <;>
      exact he.regs _ (by decide) (by decide)

/-- `save3`: our return address into the save area. -/
theorem save3_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (h12 : t.gpr .r12 = L.svb)
    (h0 : t.mem.readW (State.addr L.scr) 32 = g .lr) (h8 : Saved8 L g t.mem) :
    WP isa (.block save3) t fun t' => E L g m₀ t' ∧ Saved L g t'.mem := by
  have l20 := he.inArgs hL (k := 20) (by omega)
  have a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.scr
  have r0 : InRegions (t.rd ++ t.wr) (State.addr L.scr) 4 :=
    ⟨L.SC, by rw [he.rd, he.wr]; simp, by
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; have := hL.slen17; omega⟩
  have s32 := hL.svb_addr (k := 32) (by omega)
  have w32 := sv_in hL he (k := 32) (by omega)
  apply WP.of_runBlock
  simp only [save3, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, State.store32,
    Nat.reduceLT, ite_true, l20, a20, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, BitVec.add_zero, r0, h0,
    RegUpd.gpr_setReg, reduceCtorEq, ite_false, h12, s32, w32]
  refine ⟨he.upd hL rfl rfl rfl (fun r h₁ h₂ => by simp only [RegUpd.gpr_setReg, h₂, ite_false])
    (Frame.sv hL (Frame.refl _ _) (by omega) _), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp (disch := decide) only [rd_off, Mem.readW_writeW_self32]
  exacts [h8.r4, h8.r5, h8.r6, h8.r7, h8.r8, h8.r9, h8.r10, h8.r11]

/-! ## The blocks between the calls -/

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes): the password, and the stack arguments to push,
`c = 1` and `scratch`. -/
structure PbkArgs (L : Lay) (salt sl out ol : BitVec 32) (t : State) : Prop where
  r0 : t.gpr .r0 = L.pw
  r1 : t.gpr .r1 = L.pwl
  r2 : t.gpr .r2 = salt
  r3 : t.gpr .r3 = sl
  r10 : t.gpr .r10 = 1
  r11 : t.gpr .r11 = out
  r12 : t.gpr .r12 = ol
  lr : t.gpr .lr = L.scr

theorem sub_b (b x : BitVec 32) : b + x - b = x := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- The registers kept across the calls, and the first PBKDF2's arguments. -/
theorem pbk1Args_ok (hL : L.Ok) {t : State} (he : E L g m₀ t) (hs : Saved L g t.mem) :
    WP isa (.block pbk1Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r4 = L.b ∧
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t' := by
  have l0 := he.inArgs hL (k := 0) (by omega)
  have l4 := he.inArgs hL (k := 4) (by omega)
  have l8 := he.inArgs hL (k := 8) (by omega)
  have l20 := he.inArgs hL (k := 20) (by omega)
  have a0 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 0)) 32 = L.r := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.r
  have a4 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 4)) 32 = L.b := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.b
  have a8 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 8)) 32 = L.blen := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.blen
  have a20 : t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 20)) 32 = L.scr := by
    rw [he.sp, hL.arg_addr (by omega)]; exact he.args.scr
  apply WP.of_runBlock
  simp only [pbk1Args, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l0, l4, l8, l20, a0, a4, a8, a20, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.sp_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, ite_true, enc1, lsl7,
    sub_b]
  have r0 := (he.regs .r0 (by decide) (by decide)).trans he.g0
  have r1 := (he.regs .r1 (by decide) (by decide)).trans he.g1
  have r2 := (he.regs .r2 (by decide) (by decide)).trans he.g2
  have r3 := (he.regs .r3 (by decide) (by decide)).trans he.g3
  exact ⟨⟨he.rd, he.wr, he.sp, rfl, rfl, rfl, r0, r1, he.args, hs, Frame.mono he.frame (by simp)⟩,
    trivial, trivial, ⟨r0, r1, r2, r3, rfl, rfl, rfl, rfl⟩⟩

theorem Ctx.inArgs {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) :
    InRegions (t.rd ++ t.wr) (State.addr (t.sp + BitVec.ofNat 32 k)) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, by
    rw [hc.sp, hL.arg_addr hk]; exact Offset.contains_base _ hk (by omega)⟩

theorem Ctx.arg {t : State} (hc : Ctx L g m₀ t) (hL : L.Ok) {k : Nat} (hk : k + 4 ≤ 36) {v : BitVec 32}
    (h : t.mem.readW (State.addr L.sp + BitVec.ofNat 64 k) 32 = v) :
    t.mem.readW (State.addr (t.sp + BitVec.ofNat 32 k)) 32 = v := by
  rw [hc.sp, hL.arg_addr hk]; exact h

/-- `Ctx` after code that writes only registers other than `r4`–`r9`. -/
theorem Ctx.regs {t t' : State} (hc : Ctx L g m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hsp : t'.sp = t.sp) (hm : t'.mem = t.mem)
    (hg : ∀ r, r = .r5 ∨ r = .r6 ∨ r = .r7 ∨ r = .r8 ∨ r = .r9 → t'.gpr r = t.gpr r) : Ctx L g m₀ t' :=
  ⟨hrd.trans hc.rd, hwr.trans hc.wr, hsp.trans hc.sp, (hg _ (by simp)).trans hc.r5,
    (hg _ (by simp)).trans hc.r6, (hg _ (by simp)).trans hc.r7, (hg _ (by simp)).trans hc.r8,
    (hg _ (by simp)).trans hc.r9, by rw [hm]; exact hc.args, by rw [hm]; exact hc.saved,
    by rw [hm]; exact hc.frame⟩

/-- The arguments of a call of ROMix on the block at `cur`. -/
structure RomixArgs (L : Lay) (cur : BitVec 32) (t : State) : Prop where
  r0 : t.gpr .r0 = cur
  r1 : t.gpr .r1 = L.r
  r2 : t.gpr .r2 = L.v
  r3 : t.gpr .r3 = L.vlen
  r12 : t.gpr .r12 = L.scr
  lr : t.gpr .lr = L.r + 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block romixArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .r4 = t.gpr .r4 ∧
      RomixArgs L (t.gpr .r4) t' := by
  have l12 := hc.inArgs hL (k := 12) (by omega)
  have l16 := hc.inArgs hL (k := 16) (by omega)
  have a12 := hc.arg hL (k := 12) (by omega) hc.args.v
  have a16 := hc.arg hL (k := 16) (by omega) hc.args.vlen
  apply WP.of_runBlock
  simp only [romixArgs, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, ite_true, l12, l16, a12, a16, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq,
    ite_false, enc2, hc.r6, hc.r7]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, trivial, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem nextBlock_ok {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block nextBlock) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r4 = t.gpr .r4 + BitVec.ofNat 32 (L.r.toNat * 128) ∧
      t'.z = (t.gpr .r4 + BitVec.ofNat 32 (L.r.toNat * 128) - (L.b + BitVec.ofNat 32 (L.blen.toNat * 128)) == 0) := by
  apply WP.of_runBlock
  simp only [nextBlock, runBlock_cons, runStep_some, runBlock_nil, exec, Op2.eval, Nat.reduceLeDiff, and_self,
    ite_true, Option.map_some, Option.some.injEq, exists_eq_left', RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_setReg, reduceCtorEq, ite_false, hc.r6, lsl7, subFlags]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, trivial, ?_⟩
  · rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [hc.r5]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block pbk2Args) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧
      PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t' := by
  have l4 := hc.inArgs hL (k := 4) (by omega)
  have l8 := hc.inArgs hL (k := 8) (by omega)
  have l28 := hc.inArgs hL (k := 28) (by omega)
  have l32 := hc.inArgs hL (k := 32) (by omega)
  have a4 := hc.arg hL (k := 4) (by omega) hc.args.b
  have a8 := hc.arg hL (k := 8) (by omega) hc.args.blen
  have a28 := hc.arg hL (k := 28) (by omega) hc.args.out
  have a32 := hc.arg hL (k := 32) (by omega) hc.args.ol
  apply WP.of_runBlock
  simp only [pbk2Args, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, l4, l8, l28, l32, a4, a8, a28, a32, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq, ite_false, enc1, lsl7, hc.r7, hc.r8, hc.r9]
  refine ⟨hc.regs rfl rfl rfl rfl fun r hr => ?_, trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem restore_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block restore) t fun t' => (∀ r ∈ preserved, t'.gpr r = g r) ∧ t'.sp = t.sp ∧
      t'.mem = t.mem := by
  have s0 := hL.svb_addr (k := 0) (by omega)
  have s4 := hL.svb_addr (k := 4) (by omega)
  have s8 := hL.svb_addr (k := 8) (by omega)
  have s12 := hL.svb_addr (k := 12) (by omega)
  have s16 := hL.svb_addr (k := 16) (by omega)
  have s20 := hL.svb_addr (k := 20) (by omega)
  have s24 := hL.svb_addr (k := 24) (by omega)
  have s28 := hL.svb_addr (k := 28) (by omega)
  have s32 := hL.svb_addr (k := 32) (by omega)
  have i : ∀ k, k + 4 ≤ 36 → InRegions (t.rd ++ t.wr) (L.SVA + BitVec.ofNat 64 k) 4 := fun k hk =>
    ⟨L.SC, by rw [hc.rd, hc.wr]; simp, sv_con hL hk⟩
  have i0 := i 0 (by omega)
  have i4 := i 4 (by omega)
  have i8 := i 8 (by omega)
  have i12 := i 12 (by omega)
  have i16 := i 16 (by omega)
  have i20 := i 20 (by omega)
  have i24 := i 24 (by omega)
  have i28 := i 28 (by omega)
  have i32 := i 32 (by omega)
  apply WP.of_runBlock
  simp only [restore, runBlock_cons, runStep_some, runBlock_nil, exec, State.load32, Op2.eval,
    Nat.reduceLT, Nat.reduceLeDiff, and_self, ite_true, Option.map_some, Option.some.injEq, exists_eq_left',
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_setReg, RegUpd.sp_setReg, reduceCtorEq,
    ite_false, enc1920, hc.r6, hc.r7, s0, s4, s8, s12, s16, s20, s24, s28, s32, i0, i4, i8, i12, i16, i20,
    i24, i28, i32, hc.saved.r4, hc.saved.r5, hc.saved.r6, hc.saved.r7, hc.saved.r8, hc.saved.r9,
    hc.saved.r10, hc.saved.r11, hc.saved.lr]
  refine ⟨fun r hr => ?_, trivial⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

end VG.Proof.Scrypt.Arm.Whole
