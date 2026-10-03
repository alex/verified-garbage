import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.Rfc6979.X86_64.Hmac
import VerifiedGarbage.Proof.Weierstrass.X86_64.Words
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Deterministic ECDSA on x86-64: the blocks between the calls

`V = 0x01…` and `K = 0x00…` (`initKV_ok`), the number of candidates
(`initCnt_ok`), the message `V ‖ b (‖ d ‖ h)` in `scratch` (`msg_ok`), the
arguments of `core` (`coreArgs_ok`), whether to go on (`goOn_ok`, `again_ok`,
`stop_ok`), and the wiping of the frame (`wipe_ok`).
-/

namespace VG.Proof.Ecdsa.Rfc6979.X86_64

open VG VG.X86_64 VG.Impl.Ecdsa.Rfc6979.X86_64
open VG.Proof.Sha256.X86_64 (Compress)

variable {v : Compress} {L : Lay} {g : Reg → BitVec 64} {m₀ : Mem}

/-- The 32 bytes at `q`, each of whose words is `w`. -/
theorem bytesAt_of_readW (m : Mem) (q : Addr) (w : BitVec 64)
    (h : ∀ j < 4, m.readW (q + BitVec.ofNat 64 (8 * j)) 64 = w) :
    Spec.Sha256.bytesAt m q 32 = (List.range 32).map fun i => w.extractLsb' (8 * (i % 8)) 8 := by
  simp only [Spec.Sha256.bytesAt]
  refine List.map_congr_left fun i hi => ?_
  have hi := List.mem_range.mp hi
  rw [show i = 8 * (i / 8) + i % 8 by omega, Proof.Weierstrass.X86_64.byte_word m q (i / 8) (Nat.mod_lt _ (by decide)),
    h _ (by omega)]
  congr 2; omega

/-! ## `V` and `K` -/

theorem kvN_ok (hL : L.Ok) {u : State} (hc : Ctx L g m₀ u) {a b : BitVec 64} (ha : u.gpr .rax = a)
    (hb : u.gpr .rcx = b) : ∀ k ≤ 4,
    WP isa (.block ((List.range k).flatMap fun j => [.store (stk (fV + 8 * j)) .rax,
      .store (stk (fK + 8 * j)) .rcx])) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 64⟩] u.mem u'.mem ∧
      ∀ j < k, u'.mem.readW (L.B + BitVec.ofNat 64 (56 + 8 * j)) 64 = a ∧
        u'.mem.readW (L.B + BitVec.ofNat 64 (24 + 8 * j)) 64 = b
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hk => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (kvN_ok hL hc ha hb k (by omega)) fun u₁ ⟨hrd, hwr, hg, hf, hv⟩ => ?_
    have w₁ := hc.inFrW (d := 56 + 8 * k) (n := 8) (by omega) (by omega)
    have w₂ := hc.inFrW (d := 24 + 8 * k) (n := 8) (by omega) (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hg, hc.rsp,
      Offset.add_add, fV, fK, Nat.zero_add, show 24 + (32 + 8 * k) = 56 + 8 * k by omega, hwr, w₁, w₂, ite_true,
      Option.some.injEq, exists_eq_left', ha, hb]
    have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 160 → y + 8 ≤ 160 →
        Mem.Sep (L.B + BitVec.ofNat 64 x) (64 / 8) (L.B + BitVec.ofNat 64 y) (64 / 8) :=
      fun x y h h₁ h₂ => Offset.sep _ h (by omega) (by omega)
    refine ⟨hrd, trivial, trivial, hf.trans ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega)))), fun j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide)]
      exact hv j hj
    · rw [Mem.readW_writeW_sep (sep _ _ (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64, Mem.readW_writeW_self64]
      exact ⟨rfl, rfl⟩

theorem xor_self_zx (x : BitVec 32) : (x ^^^ x).setWidth 64 = 0 := by simp

theorem kv_bytes (m : Mem) (q : Addr) (w : BitVec 64) (o : Nat)
    (h : ∀ j < 4, m.readW (q + BitVec.ofNat 64 (o + 8 * j)) 64 = w) :
    Spec.Sha256.bytesAt m (q + BitVec.ofNat 64 o) 32 =
      (List.range 32).map fun i => w.extractLsb' (8 * (i % 8)) 8 :=
  bytesAt_of_readW m _ w fun j hj => by rw [Offset.add_add]; exact h j hj

/-- `V = 0x01…` and `K = 0x00…`. -/
theorem initKV_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.initKV) t fun t' => Ctx L g m₀ t' ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 64⟩] t.mem t'.mem ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 56) 32 = List.replicate 32 1 ∧
      Spec.Sha256.bytesAt t'.mem (L.B + BitVec.ofNat 64 24) 32 = List.replicate 32 0 := by
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  rw [Cfg.initKV, WP.block_append_iff]
  have h₁ : WP isa (.block [.movImm64 .rax (BitVec.ofNat 64 0x0101010101010101), .alu32 .xor .rcx (.reg .rcx)]) t
      fun u => Ctx L g m₀ u ∧ u.rd = t.rd ∧ u.wr = t.wr ∧ u.mem = t.mem ∧
        u.gpr .rax = BitVec.ofNat 64 0x0101010101010101 ∧ u.gpr .rcx = 0 := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false, ite_true,
      Option.some.injEq, exists_eq_left', xor_self_zx]
    exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv, by triv⟩
  refine WP.mono h₁ fun u ⟨hcu, hrd, hwr, hm, ha, hb⟩ => WP.mono (kvN_ok hL hcu ha hb 4 (by omega))
    fun u' ⟨hrd', hwr', _, hf, hv⟩ => ⟨hrd'.trans hrd, hwr'.trans hwr, hm ▸ hf, ?_, ?_⟩
  · rw [show (56 : Nat) = 56 + 0 from rfl, kv_bytes _ _ _ _ fun j hj => (hv j hj).1]; decide
  · rw [show (24 : Nat) = 24 + 0 from rfl, kv_bytes _ _ _ _ fun j hj => (hv j hj).2]; decide

/-! ## The number of candidates -/

/-- The number of candidates left, in the frame. -/
abbrev cnt (L : Lay) (m : Mem) : BitVec 64 := m.readW (L.B + BitVec.ofNat 64 120) 64

theorem initCnt_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block (cfgOf v).initCnt) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 120, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = BitVec.ofNat 64 8 := by
  have w := hc.inFrW (d := 120) (n := 8) (by omega) (by omega)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  apply WP.of_runBlock
  simp only [Cfg.initCnt, cfgOf, fCnt, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    State.store64, ea_stk, Option.map_some, RegUpd.gpr_setReg_self, RegUpd.gpr_setReg, reduceCtorEq, ite_false,
    RegUpd.wr_setReg, RegUpd.rd_setReg, RegUpd.mem_setReg, hc.rsp, Offset.add_add, Nat.reduceAdd, w, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨by triv, by triv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _), ?_⟩
  simp only [cnt, Mem.readW_writeW_self64]; rfl

/-! ## `core`'s arguments -/

theorem coreArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.coreArgs) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.gpr .rdi = L.out ∧
      t'.gpr .rsi = L.d ∧ t'.gpr .rdx = L.dg ∧ t'.gpr .rcx = L.B + BitVec.ofNat 64 56 ∧ t'.gpr .r8 = L.scr := by
  have p0 := hc.inFr (d := 152) (by omega) (by omega)
  have p1 := hc.inFr (d := 144) (by omega) (by omega)
  have p2 := hc.inFr (d := 136) (by omega) (by omega)
  have p3 := hc.inFr (d := 128) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [Cfg.coreArgs, Cfg.fr, fOut, fD, fDigest, fV, fScratch, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, State.load64, ea_stk, RegUpd.gpr_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false,
    ite_true, hc.rsp, Offset.add_add, Nat.reduceAdd, p0, p1, p2, p3, hc.pOut, hc.pD, hc.pDg, hc.pScr, sx32,
    Nat.reducePow, Nat.reduceLT, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv, by triv, by triv⟩

/-! ## Whether to go on -/

theorem sx1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide

theorem mask_true (x : BitVec 64) : x - x - (BitVec.ofBool true).setWidth 64 = BitVec.allOnes 64 := by simp
theorem mask_false (x : BitVec 64) : x - x - (BitVec.ofBool false).setWidth 64 = 0 := by simp

theorem goOn_flag (a : BitVec 32) (c : BitVec 64) (x : BitVec 64) :
    ((x - x - (BitVec.ofBool (decide (a.toNat < (1 : BitVec 32).toNat))).setWidth 64) &&& c &&&
        ((x - x - (BitVec.ofBool (decide (a.toNat < (1 : BitVec 32).toNat))).setWidth 64) &&& c) == 0) =
      !decide (a = 0 ∧ c ≠ 0) := by
  have hb : decide (a.toNat < (1 : BitVec 32).toNat) = decide (a = 0) := by
    by_cases ha : a = 0
    · subst ha; rfl
    · have : ¬ a.toNat < (1 : BitVec 32).toNat := fun h => ha (BitVec.eq_of_toNat_eq (by
        have : (1 : BitVec 32).toNat = 1 := rfl
        show a.toNat = 0; omega))
      rw [decide_eq_false this, decide_eq_false ha]
  rw [hb, BitVec.and_self]
  by_cases ha : a = 0
  · simp only [ha, decide_true, mask_true, BitVec.allOnes_and, true_and]
    by_cases hc : c = 0
    · subst hc; rfl
    · simp only [hc, decide_true, Bool.not_true, ne_eq, not_false_eq_true, beq_eq_false_iff_ne]
  · simp only [ha, decide_false, mask_false, false_and]
    simp

/-- One candidate fewer; `ZF` is clear iff the signature failed and candidates are left. -/
theorem goOn_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.goOn) t fun t' => Ctx L g m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 120, 8⟩] t.mem t'.mem ∧ cnt L t'.mem = cnt L t.mem - 1 ∧
      t'.gpr .rax = t.gpr .rax ∧
      t'.zf = some (!decide ((t.gpr .rax).setWidth 32 = 0 ∧ cnt L t.mem - 1 ≠ 0)) := by
  have r := hc.inFr (d := 120) (by omega) (by omega)
  have w := hc.inFrW (d := 120) (n := 8) (by omega) (by omega)
  refine Ctx.of_keep hL hc ?_ (by rfl) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  apply WP.of_runBlock
  simp only [Cfg.goOn, fCnt, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execAlu32, readSrc, readSrc32,
    State.load64, State.store64, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.cf_setReg,
    RegUpd.cf_arithFlags, RegUpd.zf_arithFlags, Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true,
    hc.rsp, Offset.add_add, Nat.reduceAdd, r, w, sx1, Option.some.injEq, exists_eq_left']
  refine ⟨by triv, by triv, (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _), ?_,
    by triv, ?_⟩
  · simp only [cnt, Mem.readW_writeW_self64]
  · rw [goOn_flag]

/-- `ZF` clear. -/
theorem again_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.again) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some false := by
  apply WP.of_runBlock
  simp only [Cfg.again, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, RegUpd.zf_arithFlags, ite_true,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), rfl, by decide⟩

/-- `ZF` set. -/
theorem stop_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.stop) t fun t' => Ctx L g m₀ t' ∧ t'.mem = t.mem ∧ t'.zf = some true ∧
      t'.gpr .rax = t.gpr .rax := by
  apply WP.of_runBlock
  simp only [Cfg.stop, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), rfl, by simp, RegUpd.gpr_setReg_of_ne _ _ (by decide)⟩

/-! ## Wiping the frame -/

theorem zeroN_ok {u : State} (hc : Ctx L g m₀ u) : ∀ k ≤ 12,
    WP isa (.block ((List.range k).map fun j => .store (stk (8 * j)) .rcx)) u fun u' =>
      u'.rd = u.rd ∧ u'.wr = u.wr ∧ u'.gpr = u.gpr ∧ Frame [⟨L.B + BitVec.ofNat 64 24, 96⟩] u.mem u'.mem
  | 0, _ => WP.of_runBlock ⟨u, rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  | k + 1, hk => by
    rw [List.range_succ, List.map_append, List.map_singleton, WP.block_append_iff]
    refine WP.mono (zeroN_ok hc k (by omega)) fun u₁ ⟨hrd, hwr, hg, hf⟩ => ?_
    have w := hc.inFrW (d := 24 + 8 * k) (n := 8) (by omega) (by omega)
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, State.store64, ea_stk, hg, hc.rsp,
      Offset.add_add, hwr, w, ite_true, Option.some.injEq, exists_eq_left']
    exact ⟨hrd, trivial, trivial, hf.trans ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains _ (by omega) (by omega) (by omega)))⟩

/-- `K`, `V`, `h` and the count cleared, keeping `rax`. -/
theorem wipe_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) :
    WP isa (.block Cfg.wipe) t fun t' => Ctx L g m₀ t' ∧ t'.gpr .rax = t.gpr .rax ∧
      Frame [⟨L.B + BitVec.ofNat 64 24, 96⟩] t.mem t'.mem := by
  have h := Ctx.of_keep (Q := fun t' => t'.gpr .rax = t.gpr .rax) hL hc (is := Cfg.wipe)
    (ws := [⟨L.B + BitVec.ofNat 64 24, 96⟩]) ?_ (by rfl) fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact safe_low L (by omega)
  · exact WP.mono h fun _ ⟨hc', hf, ha⟩ => ⟨hc', ha, hf⟩
  rw [Cfg.wipe, WP.block_append_iff]
  have h₁ : WP isa (.block [.alu32 .xor .rcx (.reg .rcx)]) t fun u => Ctx L g m₀ u ∧ u.rd = t.rd ∧
      u.wr = t.wr ∧ u.mem = t.mem ∧ u.gpr .rax = t.gpr .rax := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu32, readSrc32, State.setReg32,
      Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false,
      Option.some.injEq, exists_eq_left']
    exact ⟨hc.regs hL rfl rfl rfl (by cs_tac), by triv, by triv, by triv, by triv⟩
  exact WP.mono h₁ fun u ⟨hcu, hrd, hwr, hm, ha⟩ => WP.mono (zeroN_ok hcu 12 (by omega))
    fun u' ⟨hrd', hwr', hg, hf⟩ => ⟨hrd'.trans hrd, hwr'.trans hwr, hm ▸ hf, by rw [hg, ha]⟩

end VG.Proof.Ecdsa.Rfc6979.X86_64
