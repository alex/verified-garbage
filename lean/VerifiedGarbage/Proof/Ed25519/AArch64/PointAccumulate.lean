import VerifiedGarbage.Impl.Ed25519.AArch64.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Ed25519.AArch64.PointSelect
import VerifiedGarbage.Proof.Ed25519.AArch64.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-! Untrusted: one masked point addition, with all memory indices public. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open Word64

theorem scalarBitMask_ok {s : State} {base : Addr} (hs : Scr s base)
    (j start bit : Nat) (hi : start + j < 512) (hbit : bit < 2)
    (hj : s.gpr .x19 = BitVec.ofNat 64 j) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit) :
    WP isa (.block scalarBitMask) s fun t =>
      t.gpr .x3 = mask (decide (bit = 0)) ∧ Keeps [.x8, .x3] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (start + j))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + (BitVec.ofNat 64 j + BitVec.ofNat 64 start) + BitVec.ofNat 64 768 =
      off base (768 + (start + j)) := by
    rw [← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hm : ((BitVec.ofNat 8 bit).setWidth 32).setWidth 64 - BitVec.ofNat 64 1 = mask (decide (bit = 0)) := by
    have h : bit = 0 ∨ bit = 1 := by omega
    rcases h with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [scalarBitMask, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    State.load, addr, Size.bits, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.rd_write, RegUpd.wr_write, BitVec.setWidth_eq,
    show (1 : Nat) < 4096 from by decide, Nat.reduceMod, Nat.reduceMul, Nat.reduceLT,
    and_self, hj, hstart, hs.x0, he, hr, read_byte, hb, hm,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨True.intro, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem Keep.of_table {base : Addr} {s t : State}
    (h : TableKeep base 64 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.sp, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : env t.mem base i = env s.mem base i :=
  Outside_F hk.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

theorem savedPoint_congr (e f : Env) (h : ∀ i : Slot, 16 ≤ i.val → e i = f i) :
    point e 17 18 19 20 = point f 17 18 19 20 := by
  simp only [point, h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide)]

theorem copyPointToQ_saved (e : Env) : point (evalOps copyPointToQOps e) 17 18 19 20 = point e 17 18 19 20 := rfl

theorem restorePoint_saved (e : Env) : point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 := rfl

theorem restorePoint_q (e : Env) : point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

theorem prepareAdd_ok {s : State} {base : Addr} (hs : Scr s base)
    (j : Nat) (hj : j < 16) (hc : s.gpr .x19 = BitVec.ofNat 64 j) :
    WP isa (.block prepareAdd) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base (5376 + 128 * j) ∧
      point (env t.mem base) 17 18 19 20 = point (env s.mem base) 0 1 2 3 ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [prepareAdd, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCode_ok savePointOps hs) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (ka.scr hs).x0 5376 j (by omega)
    ((ka.gpr _ (by decide)).trans hc)) fun b ⟨pb, kb⟩ => ?_
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTable_ok ((ka.trans kbe).scr hs) pb (by omega) (by omega))
    fun c ⟨pc, kc⟩ => ?_
  have kce := Keep.of_table kc
  have cs : point (env c.mem base) 17 18 19 20 = point (env s.mem base) 0 1 2 3 := by
    rw [savedPoint_congr _ _ (fun i hi => tableLoad_high kc i (by omega)), kb.mem, va, savePoint_eval]
  have cd : env c.mem base 16 = env s.mem base 16 := by
    rw [tableLoad_high kc 16 (by decide), kb.mem, va]; rfl
  have cq : point (env c.mem base) 0 1 2 3 = tablePoint s.mem base (5376 + 128 * j) := by
    rw [pc, kb.mem]
    exact workspace_tablePoint ka.mem (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (fieldCode_ok copyPointToQOps (((ka.trans kbe).trans kce).scr hs))
    fun d ⟨kd, vd⟩ => ?_
  refine WP.mono (fieldCode_ok restorePointOps ((((ka.trans kbe).trans kce).trans kd).scr hs))
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨(((ka.trans kbe).trans kce).trans kd).trans kt, ?_, ?_, ?_, ?_⟩
  · rw [vt, restorePoint_eval, vd, copyPointToQ_saved, cs]
  · rw [vt, restorePoint_q, vd, copyPointToQ_eval, cq]
  · rw [vt, restorePoint_saved, vd, copyPointToQ_saved, cs]
  · rw [vt, vd]
    exact cd

theorem Keep.bit {base : Addr} {s t : State} (h : Keep base s t) (i : Nat) (hi : i < 512) :
    t.mem (off base (768 + i)) = s.mem (off base (768 + i)) :=
  h.mem _ (by rw [ofs_off' base (by omega)]; omega)

theorem pointAccumulate_ok {s : State} {base : Addr} (hs : Scr s base)
    (j start bit : Nat) (hj : j < 16) (hi : start + j < 512) (hbit : bit < 2)
    (hc : s.gpr .x19 = BitVec.ofNat 64 j) (hstart : s.gpr .x1 = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block pointAccumulate) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 =
        (if bit = 0 then point (env s.mem base) 0 1 2 3 else
          Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (tablePoint s.mem base (5376 + 128 * j))) ∧
      env t.mem base 16 = Spec.Ed25519.d := by
  rw [pointAccumulate, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (prepareAdd_ok hs j hj hc) fun a ⟨ka, ap, aq, av, ad⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointAdd_ok (ka.scr hs) (ad.trans hd)) fun b ⟨kb, bp, bh⟩ => ?_
  have kab := ka.trans kb
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (kab.scr hs) j start bit hi hbit
    ((kab.gpr _ (by decide)).trans hc) ((kab.gpr _ (by decide)).trans hstart)
    ((kab.bit _ hi).trans hb)) fun c ⟨cm, kc⟩ => ?_
  have kce : Keep base b c := Keep.of_keeps kc (by decide)
  refine WP.mono (pointSelect_ok ((kab.trans kce).scr hs) cm) fun t ⟨kt, tv, td⟩ => ?_
  refine ⟨(kab.trans kce).trans kt, ?_, ?_⟩
  · rw [tv, kc.mem, savedPoint_congr _ _ bh, av, bp, ap, aq]
    simp only [decide_eq_true_eq]
  · rw [td, kc.mem, bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.AArch64
