import VerifiedGarbage.Impl.Ed25519.X86_64.PointAccumulate
import VerifiedGarbage.Proof.Ed25519.X86_64.PointSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.PointTableAddr
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowers

/-! One masked point addition, with all memory indices public. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off mask Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem scalarBitMask_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j start bit : Nat) (hi : start + j < 512) (hbit : bit < 2)
    (hj : s.gpr .rbx = BitVec.ofNat 64 j) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit) :
    WP isa (.block scalarBitMask) s fun t =>
      t.gpr .rcx = mask (decide (bit = 0)) ∧ Keeps [.rax, .rcx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base (768 + (start + j))) 1 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : base + (BitVec.ofNat 64 j + BitVec.ofNat 64 start) * 1#64 + BitVec.ofInt 64 768 =
      off base (768 + (start + j)) := by
    rw [BitVec.mul_one, ← BitVec.ofNat_add, show BitVec.ofInt 64 768 = BitVec.ofNat 64 768 from rfl,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    exact congrArg (off base) (by omega)
  have hm : (BitVec.ofNat 8 bit).setWidth 64 - (1 : BitVec 32).signExtend 64 = mask (decide (bit = 0)) := by
    have h : bit = 0 ∨ bit = 1 := by omega
    rcases h with rfl | rfl <;> decide
  apply WP.of_runBlock
  simp only [scalarBitMask, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load8, State.ea, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg,
    RegUpd.mem_arithFlags, RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg,
    RegUpd.wr_arithFlags, hj, hstart, hs.rdi, he, hr, hb, hm,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2, ite_false]

theorem Keep.of_table {base : Addr} {s t : State}
    (h : TableKeep base 64 128 s t) : Keep base s t := by
  refine ⟨fun r hr => h.gpr r (fun hm => hr ?_), h.rd, h.wr, h.mem.mono (by decide) (by decide)⟩
  exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm

theorem tableLoad_high {base : Addr} {s t : State} (hk : TableKeep base 64 128 s t)
    (i : Slot) (hi : 4 ≤ i.val) : env t.mem base i = env s.mem base i :=
  Outside_F hk.mem (by simp only [offset]; omega) (Or.inr (by simp only [offset]; omega))

theorem savedPoint_congr (e f : Env) (h : ∀ i : Slot, 16 ≤ i.val → e i = f i) :
    point e 17 18 19 20 = point f 17 18 19 20 := by
  simp only [point, h 17 (by decide), h 18 (by decide), h 19 (by decide), h 20 (by decide)]

theorem copyPointToQ_saved (e : Env) : point (evalOps copyPointToQOps e) 17 18 19 20 = point e 17 18 19 20 := rfl

theorem restorePoint_saved (e : Env) : point (evalOps restorePointOps e) 17 18 19 20 = point e 17 18 19 20 := rfl

theorem restorePoint_q (e : Env) : point (evalOps restorePointOps e) 4 5 6 7 = point e 4 5 6 7 := rfl

theorem prepareAdd_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 16) (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (prepareAdd fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      point (env t.mem base) 4 5 6 7 = tablePoint s.mem base (5376 + 128 * j) ∧
      point (env t.mem base) 17 18 19 20 = point (env s.mem base) 0 1 2 3 ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [prepareAdd, List.append_assoc, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs savePointOps) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (hs.of_keep ka).rdi 5376 j (by omega)
    ((ka.gpr _ (by decide)).trans hc)) fun b ⟨pb, kb⟩ => ?_
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (pointFromTable_ok (hs.of_keep (ka.trans kbe)) pb (by omega) (by omega))
    fun c ⟨pc, kc⟩ => ?_
  have kce := Keep.of_table kc
  have cs : point (env c.mem base) 17 18 19 20 = point (env s.mem base) 0 1 2 3 := by
    rw [savedPoint_congr _ _ (fun i hi => tableLoad_high kc i (by omega)), kb.2.1, va, savePoint_eval]
  have cd : env c.mem base 16 = env s.mem base 16 := by
    rw [tableLoad_high kc 16 (by decide), kb.2.1, va]; rfl
  have cq : point (env c.mem base) 0 1 2 3 = tablePoint s.mem base (5376 + 128 * j) := by
    rw [pc, kb.2.1]
    exact workspace_tablePoint ka.mem (by omega) (by omega)
  rw [WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok (hs.of_keep ((ka.trans kbe).trans kce)) copyPointToQOps)
    fun d ⟨kd, vd⟩ => ?_
  refine WP.mono (fieldCodeWide_ok (hs.of_keep (((ka.trans kbe).trans kce).trans kd)) restorePointOps)
    fun t ⟨kt, vt⟩ => ?_
  refine ⟨(((ka.trans kbe).trans kce).trans kd).trans kt, ?_, ?_, ?_, ?_⟩
  · rw [vt, restorePoint_eval, vd, copyPointToQ_saved, cs]
  · rw [vt, restorePoint_q, vd, copyPointToQ_eval, cq]
  · rw [vt, restorePoint_saved, vd, copyPointToQ_saved, cs]
  · rw [vt, vd]
    exact cd

theorem Keep.bit {base : Addr} {s t : State} (h : Keep base s t) (i : Nat) (hi : i < 512) :
    t.mem (off base (768 + i)) = s.mem (off base (768 + i)) :=
  h.mem _ (by rw [Proof.X25519.X86_64.ofs_off' base (by omega)]; omega)

theorem pointAccumulate_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j start bit : Nat) (hj : j < 16) (hi : start + j < 512) (hbit : bit < 2)
    (hc : s.gpr .rbx = BitVec.ofNat 64 j) (hstart : s.gpr .rsi = BitVec.ofNat 64 start)
    (hb : s.mem (off base (768 + (start + j))) = BitVec.ofNat 8 bit)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block (pointAccumulate fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 =
        (if bit = 0 then point (env s.mem base) 0 1 2 3 else
          Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (tablePoint s.mem base (5376 + 128 * j))) ∧
      env t.mem base 16 = Spec.Ed25519.d := by
  rw [pointAccumulate, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (prepareAdd_ok hs j hj hc) fun a ⟨ka, ap, aq, av, ad⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pointAddWide_ok (hs.of_keep ka) (ad.trans hd)) fun b ⟨kb, bp, bh⟩ => ?_
  have kab := ka.trans kb
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitMask_ok (hs.of_keep kab) j start bit hi hbit
    ((kab.gpr _ (by decide)).trans hc) ((kab.gpr _ (by decide)).trans hstart)
    ((kab.bit _ hi).trans hb)) fun c ⟨cm, kc⟩ => ?_
  have kce : Keep base b c := Keep.of_keeps kc (by decide)
  refine WP.mono (pointSelect_ok (hs.of_keep (kab.trans kce)) cm) fun t ⟨kt, tv, td⟩ => ?_
  refine ⟨(kab.trans kce).trans kt, ?_, ?_⟩
  · rw [tv, kc.2.1, savedPoint_congr _ _ bh, av, bp, ap, aq]
    simp only [decide_eq_true_eq]
  · rw [td, kc.2.1, bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.X86_64
