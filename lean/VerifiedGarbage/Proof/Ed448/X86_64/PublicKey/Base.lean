import VerifiedGarbage.Proof.Ed448.X86_64.PublicKey.Hash
import VerifiedGarbage.Proof.Ed448.Prune
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLoop
import VerifiedGarbage.Proof.Ed448.X86_64.BaseVerified

/-!
# Ed448 public-key derivation on x86-64: pruning and the base point

The first 57 bytes of the hash, pruned, are stored in the frame
(`prune_ok`), `[s]B` is encoded into `out` (`base_ok`), and the frame's copy
of `s` is cleared (`wipe_ok`).
-/

namespace VG.Proof.Ed448.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed448.X86_64
open VG.Proof.Ed448 (prune_nat)

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Arithmetic -/

/-- The 57 bytes at `p`: seven words and a byte. -/
theorem decode57 (m : Mem) (p : Addr) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 57) =
      (m.readW p 64).toNat + 2 ^ 64 * ((m.readW (p + BitVec.ofNat 64 8) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 16) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 24) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 32) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 40) 64).toNat + 2 ^ 64 *
      ((m.readW (p + BitVec.ofNat 64 48) 64).toNat + 2 ^ 64 *
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 56) 1))))))) := by
  have e0 := words_step m p 57 0 (by omega)
  have e1 := words_step m p 57 1 (by omega)
  have e2 := words_step m p 57 2 (by omega)
  have e3 := words_step m p 57 3 (by omega)
  have e4 := words_step m p 57 4 (by omega)
  have e5 := words_step m p 57 5 (by omega)
  have e6 := words_step m p 57 6 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.mul_zero, Nat.sub_zero] at e0 e1 e2 e3 e4 e5 e6
  rw [BitVec.add_zero] at e0
  rw [e0, e1, e2, e3, e4, e5, e6]

/-- The byte below a word that is zero. -/
theorem byte_of_zero (m : Mem) (p : Addr) (h : m.readW p 64 = 0) :
    Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 1) = 0 := by
  have hs : Spec.Ed448.bytesAt m p (1 + 7) =
      Spec.Ed448.bytesAt m p 1 ++ Spec.Ed448.bytesAt m (p + BitVec.ofNat 64 1) 7 :=
    Proof.X25519.bytesAt_add m p 1 7
  have hw : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 8) = 0 := by
    rw [Proof.Ed448.decodeLE_eq, Proof.Ed448.bytesAt_eq, Proof.X25519.leNum_bytesAt_64, h]; rfl
  rw [show (8 : Nat) = 1 + 7 from rfl, hs, Proof.Ed448.decodeLE_append] at hw
  omega

/-! ## Stores into the frame -/

/-- Code that writes only caller-saved registers and the frame's scalar. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem) : Ctx L g mx m₀ t' := by
  have keep : ∀ d, 80 ≤ d → d + 8 ≤ 104 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 80 (by omega) (by omega)).trans hc.pScr, (keep 88 (by omega) (by omega)).trans hc.pSeed,
    (keep 96 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩)⟩

theorem st_ok {t : State} (hc : Ctx L g mx m₀ t) {k : Nat} (hk : k < 8) (r : Reg) :
    WP isa (.block [Instr.store (stk (8 * k)) r]) t fun t' =>
      t'.mem = t.mem.writeW (L.B + BitVec.ofNat 64 (16 + 8 * k)) (t.gpr r) ∧ t'.gpr = t.gpr ∧
        t'.rd = t.rd ∧ t'.wr = t.wr ∧ t'.mxcsr = t.mxcsr := by
  have w := hc.inFrW (d := 16 + 8 * k) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hc.rsp, add_add, w,
    ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

/-- The first `n` stores of `pkStores`. -/
abbrev storesN (n : Nat) : List Instr := (List.range n).map fun k => .store (stk (8 * k)) (pkRegs.getD k .r8)

theorem stores_ok : ∀ n ≤ 8, ∀ t : State, Ctx L g mx m₀ t →
    WP isa (.block (storesN n)) t fun t' => Ctx L g mx m₀ t' ∧ t'.gpr = t.gpr ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem ∧
      ∀ j < n, t'.mem.readW (L.B + BitVec.ofNat 64 (16 + 8 * j)) 64 = t.gpr (pkRegs.getD j .r8)
  | 0, _, _, hc => WP.block_nil ⟨hc, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn, t, hc => by
    rw [storesN, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (stores_ok n (by omega) t hc) fun u ⟨hu, ug, uf, uw⟩ => ?_
    refine WP.mono (st_ok hu (k := n) (by omega) _) fun v ⟨vm, vg, vrd, vwr, vmx⟩ => ?_
    have hf1 : Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] u.mem v.mem := by
      rw [vm]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains _ (by omega) (by omega)
        (by omega))
    refine ⟨hu.store vrd vwr vmx (fun r _ => by rw [vg]) hf1, by rw [vg, ug], uf.trans hf1, fun j hj => ?_⟩
    rw [vm]
    by_cases hjn : j = n
    · subst hjn; rw [Mem.readW_writeW_self64, ug]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide), uw j (by omega)]

/-! ## Pruning -/

/-- Word `k` of the hash. -/
abbrev hw (t : State) (L : Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.scr + BitVec.ofNat 64 (1024 + 8 * k)) 64

/-- `rdx = scratch`. -/
theorem rdx_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block [Instr.mov .rdx (.mem (stk fScratch))]) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .rdx = L.scr := by
  have h80 := hc.inFr (d := 80) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_stk,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, Option.map_some, ite_true, hc.rsp, add_add, Nat.reduceAdd, h80,
    hc.pScr, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial⟩

theorem loads_ok {t : State} (hc : Ctx L g mx m₀ t) (hdx : t.gpr .rdx = L.scr) :
    WP isa (.block pkLoads) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = hw t L 0 ∧ t'.gpr .r9 = hw t L 1 ∧ t'.gpr .r10 = hw t L 2 ∧ t'.gpr .r11 = hw t L 3 ∧
      t'.gpr .rax = hw t L 4 ∧ t'.gpr .rcx = hw t L 5 ∧ t'.gpr .rsi = hw t L 6 := by
  have s0 := hc.inScr (o := 1024) (by omega)
  have s1 := hc.inScr (o := 1032) (by omega)
  have s2 := hc.inScr (o := 1040) (by omega)
  have s3 := hc.inScr (o := 1048) (by omega)
  have s4 := hc.inScr (o := 1056) (by omega)
  have s5 := hc.inScr (o := 1064) (by omega)
  have s6 := hc.inScr (o := 1072) (by omega)
  apply WP.of_runBlock
  simp only [pkLoads, hashWord, hashAt, Nat.reduceMul, Nat.reduceAdd, runBlock_cons, runStep_some,
    runBlock_nil, exec, readSrc, State.load64, ea_base, RegUpd.gpr_setReg, RegUpd.rd_setReg,
    RegUpd.wr_setReg, RegUpd.mem_setReg, Option.map_some, reduceCtorEq, ite_false, ite_true, hdx,
    s0, s1, s2, s3, s4, s5, s6, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial, trivial, trivial, trivial,
    trivial⟩

theorem mods_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkMods) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧
      t'.gpr .r8 = (t.gpr .r8 &&& BitVec.ofNat 64 (2 ^ 64 - 4)) ∧ t'.gpr .r9 = t.gpr .r9 ∧
      t'.gpr .r10 = t.gpr .r10 ∧ t'.gpr .r11 = t.gpr .r11 ∧ t'.gpr .rax = t.gpr .rax ∧
      t'.gpr .rcx = t.gpr .rcx ∧ t'.gpr .rsi = (t.gpr .rsi ||| BitVec.ofNat 64 (2 ^ 63)) ∧
      t'.gpr .rdi = 0 := by
  apply WP.of_runBlock
  simp only [pkMods, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags,
    RegUpd.mem_arithFlags, Option.map_some, Option.bind_some,
    reduceCtorEq, ite_false, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-4)) = BitVec.ofNat 64 (2 ^ 64 - 4)),
    trivial, trivial, trivial, trivial, trivial, trivial, rfl⟩

theorem take57 (m : Mem) (p : Addr) :
    (Spec.Sha3.bytesAt m p 114).take 57 = Spec.Ed448.bytesAt m p 57 := by
  simp [Spec.Sha3.bytesAt, Spec.Ed448.bytesAt, ← List.map_take, List.take_range]

theorem decodeLE_byte_lt (m : Mem) (p : Addr) : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt m p 1) < 256 := by
  simp only [Spec.Ed448.bytesAt, List.range_one, List.map_cons, List.map_nil, Spec.Ed448.decodeLE]
  have := (m (p + BitVec.ofNat 64 0)).isLt
  omega

/-- The loads, the pruning and the stores, with `rdx = scratch`. -/
theorem pruneRest_ok {t₀ : State} (hc₀ : Ctx L g mx m₀ t₀) (hd₀ : t₀.gpr .rdx = L.scr) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t₀.mem (L.scr + BitVec.ofNat 64 1024) 114 = h) :
    WP isa (.block (pkLoads ++ (pkMods ++ pkStores))) t₀ fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 57) = Spec.Ed448.prune h := by
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hc₀ hd₀) fun u ⟨hu, hmu, u8, u9, u10, u11, uax, ucx, usi⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (mods_ok hu) fun v ⟨hv, hmv, v8, v9, v10, v11, vax, vcx, vsi, vdi⟩ => ?_
  refine WP.mono (stores_ok 8 (by omega) v hv) fun w ⟨hw', _, _, ww⟩ => ⟨hw', ?_⟩
  have f0 : w.mem.readW (L.B + BitVec.ofNat 64 16) 64 = v.gpr .r8 := ww 0 (by omega)
  have f1 : w.mem.readW (L.B + BitVec.ofNat 64 24) 64 = v.gpr .r9 := ww 1 (by omega)
  have f2 : w.mem.readW (L.B + BitVec.ofNat 64 32) 64 = v.gpr .r10 := ww 2 (by omega)
  have f3 : w.mem.readW (L.B + BitVec.ofNat 64 40) 64 = v.gpr .r11 := ww 3 (by omega)
  have f4 : w.mem.readW (L.B + BitVec.ofNat 64 48) 64 = v.gpr .rax := ww 4 (by omega)
  have f5 : w.mem.readW (L.B + BitVec.ofNat 64 56) 64 = v.gpr .rcx := ww 5 (by omega)
  have f6 : w.mem.readW (L.B + BitVec.ofNat 64 64) 64 = v.gpr .rsi := ww 6 (by omega)
  have f7 : w.mem.readW (L.B + BitVec.ofNat 64 72) 64 = v.gpr .rdi := ww 7 (by omega)
  rw [decode57]
  simp only [add_add, Nat.reduceAdd]
  rw [f0, f1, f2, f3, f4, f5, f6, byte_of_zero _ _ (f7.trans vdi), v8, v9, v10, v11, vax, vcx, vsi, u8, u9,
    u10, u11, uax, ucx, usi, Spec.Ed448.prune, ← hh, take57, decode57]
  simp only [hw, add_add, Nat.reduceMul, Nat.reduceAdd]
  refine Eq.trans ?_ (prune_nat _ _ _ _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
    (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)).symm
  have c₁ : (2 ^ 64 - 4) % 2 ^ 64 = 2 ^ 64 - 4 := by decide
  have c₂ : 2 ^ 63 % 2 ^ 64 = 2 ^ 63 := by decide
  rw [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, c₁, c₂]

theorem prune_ok {t : State} (hc : Ctx L g mx m₀ t) {h : List Byte}
    (hh : Spec.Sha3.bytesAt t.mem (L.scr + BitVec.ofNat 64 1024) 114 = h) :
    WP isa pkPrune t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 57) = Spec.Ed448.prune h :=
  WP.seq (WP.mono (rdx_ok hc) fun _ ⟨hc₀, hm₀, hd₀⟩ => pruneRest_ok hc₀ hd₀ (hm₀ ▸ hh))

/-! ## The base point -/

/-- The arguments of `vg_ed448_scalar_base`. -/
def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkBaseArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' := by
  have l80 := hc.inFr (d := 80) (by omega) (by omega)
  have l96 := hc.inFr (d := 96) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkBaseArgs, fOut, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, l80, l96,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial⟩

theorem base_nosp : NoSp scalarBase := by
  have : ((instrs scalarBase).all fun i => !Taint.clobbers i .rsp) = true := by
    rw [← Code.allInstrs_eq]; lit_decide
  intro i hi; simpa using List.all_eq_true.mp this i hi

theorem base_depth : scalarBase.depth ≤ 1 := by lit_decide

abbrev baseRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 57⟩]
abbrev baseWr (L : Lay) : List Region := [L.OUT, L.SCR]

theorem base_regs {t : State} (ha : BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 16 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem base_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    Proof.Ed448.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := base_regs ha (baseRd L) (baseWr L)
  simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, g3, rsp_ce, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, hL.stk_SCR (by omega), hL.stk_OUT (by omega), hL.stk_SCR (by omega), hL.oc, hL.nc⟩

theorem base_sub : ∀ r ∈ baseRd L ++ baseWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_stk _ (by omega) (by omega)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem base_wsub : ∀ r ∈ baseWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (within_base _ (by omega))
  · exact .inr (within_base _ (by omega))

theorem base_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) {s : Nat}
    (hs : Spec.Ed448.decodeLE (Spec.Ed448.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 57) = s) :
    WP isa (.call "vg_ed448_scalar_base" scalarBase) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed448.bytesAt t'.mem L.out 57 =
        Spec.Ed448.encodePoint (Spec.Ed448.pointMul s Spec.Ed448.basePoint) := by
  refine call_ok hL Proof.Ed448.X86_64.scalarBase_ok base_nosp base_depth hc
    (base_pre hL hc ha) base_sub base_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨g1, g2, -⟩ := base_regs ha (baseRd L) (baseWr L)
  have h := hpost
  simp only [Proof.Ed448.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed448.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 57 =
      Spec.Ed448.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 57 := by
    simp only [Spec.Ed448.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 57⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by show (57 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, Spec.Ed448.scalarBase, hs]

/-! ## Clearing the scalar -/

theorem zero_regs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block (pkRegs.map fun r => Instr.mov32 r (.imm 0))) t fun t' =>
      Ctx L g mx m₀ t' ∧ t'.mem = t.mem := by
  apply WP.of_runBlock
  simp only [pkRegs, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32,
    State.setReg32, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), rfl⟩

theorem wipe_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkWipe) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 64⟩] t.mem t'.mem := by
  rw [pkWipe, WP.block_append_iff]
  refine WP.mono (zero_regs_ok hc) fun u ⟨hu, hm⟩ => ?_
  exact WP.mono (stores_ok 8 (by omega) u hu) fun u' ⟨hu', _, hf, _⟩ => ⟨hu', hm ▸ hf⟩

end VG.Proof.Ed448.X86_64.PublicKey
