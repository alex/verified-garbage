import VerifiedGarbage.Impl.Ed25519.X86_64.PointBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul

/-! Merged from `Proof.Ed25519.X86_64.PointBatch`. -/
section
/-! The local table preserves the accumulator, bits, and checkpoints. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps clob)

variable {fld : Arith} [EdArith fld]

theorem PowersKeep.of_keep {base : Addr} {o n : Nat} {s t : State} (h : Keep base s t) :
    PowersKeep base o n s t := ⟨fun r _ _ hr => h.gpr r hr, h.rd, h.wr, TableFrame.workspace h.mem⟩

theorem loadCheckpoint_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.gpr .rbx = BitVec.ofNat 64 j) :
    WP isa (.block (loadCheckpoint fld)) s fun t => Keep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base (1280 + 128 * j) ∧
      point (env t.mem base) 17 18 19 20 = point (env s.mem base) 0 1 2 3 ∧
      env t.mem base 16 = env s.mem base 16 := by
  rw [loadCheckpoint, List.append_assoc, WP.block_append_iff]
  refine WP.mono (fieldCodeWide_ok hs savePointOps) fun a ⟨ka, va⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (hs.of_keep ka).rdi 1280 j (by omega)
    ((ka.gpr _ (by decide)).trans hc)) fun b ⟨pb, kb⟩ => ?_
  have kbe : Keep base a b := Keep.of_keeps kb (by decide)
  refine WP.mono (pointFromTable_ok (hs.of_keep (ka.trans kbe)) pb (by omega) (by omega))
    fun t ⟨pt, kt⟩ => ?_
  refine ⟨(ka.trans kbe).trans (Keep.of_table kt), ?_, ?_, ?_⟩
  · rw [pt, kb.2.1]; exact workspace_tablePoint ka.mem (by omega) (by omega)
  · rw [savedPoint_congr _ _ (fun i hi => tableLoad_high kt i (by omega)), kb.2.1, va, savePoint_eval]
  · rw [tableLoad_high kt 16 (by decide), kb.2.1, va]; rfl

theorem prepareBatch_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.gpr .rbx = BitVec.ofNat 64 j)
    (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (prepareBatch fld) s fun t => PowersKeep base 5376 2048 s t ∧
      point (env t.mem base) 0 1 2 3 = point (env s.mem base) 0 1 2 3 ∧
      (∀ i < 16, tablePoint t.mem base (5376 + 128 * i) =
        powerPoint (tablePoint s.mem base (1280 + 128 * j)) i) ∧
      env t.mem base 16 = Spec.Ed25519.d := by
  rw [prepareBatch]
  refine WP.seq (WP.mono (loadCheckpoint_ok hs j hj hc) fun a ⟨ka, ap, av, ad⟩ => ?_)
  refine WP.seq (WP.mono (pointPowers_ok false (hs.of_keep ka) 5376 16 (by decide)
    (by decide) (by decide) (by decide) (ad.trans hd)) fun b ⟨bt, _, bh, kb⟩ => ?_)
  refine WP.mono (fieldCodeWide_ok (kb.scratch (hs.of_keep ka)) restorePointOps) fun t ⟨kt, vt⟩ => ?_
  refine ⟨((PowersKeep.of_keep ka).trans kb).trans (PowersKeep.of_keep kt), ?_, ?_, ?_⟩
  · rw [vt, restorePoint_eval, savedPoint_congr _ _ bh, av]
  · intro i hi
    rw [workspace_tablePoint kt.mem (by omega) (by omega), bt i hi, ap]
    simp only [powerStride, Bool.false_eq_true, ite_false, Nat.one_mul]
  · rw [vt]
    change env b.mem base 16 = _
    rw [bh 16 (by decide), ad, hd]

end VG.Proof.Ed25519.X86_64
end

/-! The public batch counter survives field and table operations. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Outside Keeps ea_sc)

theorem tableFrame_outside {base : Addr} {o n : Nat} {m m' : Mem}
    (h : TableFrame base o n m m') (ho : 64 ≤ o) (hn : 768 ≤ o + n) :
    Outside base 64 (o + n - 64) m m' := by
  intro p hp
  exact h p (by omega) (by omega)

theorem batchBegin_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 (j + 1)) :
    WP isa (.block batchBegin) s fun t =>
      t.gpr .rbx = BitVec.ofNat 64 j ∧ t.mem.readW (off base 56) 64 = BitVec.ofNat 64 j ∧
      (∀ r, r ≠ .rbx → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      Outside base 56 8 s.mem t.mem := by
  have hw : InRegions s.wr (off base 56) 8 :=
    ⟨_, hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have he : BitVec.ofNat 64 (j + 1) - (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 j := by
    rw [show (1 : BitVec 32).signExtend 64 = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add, BitVec.add_sub_cancel]
  apply WP.of_runBlock
  simp only [batchBegin, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, State.store64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.rd_arithFlags, RegUpd.wr_setReg, RegUpd.wr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_arithFlags, hs.rdi, hr, hw, hc, he,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_, fun r hr => ?_, trivial, trivial, ?_⟩
  · exact Mem.readW_writeW_self64 _ _ _
  · simp only [hr, ite_false]
  · intro p hp
    exact VG.Proof.X25519.X86_64.writeW_outside _ _ _ (by decide) p hp

theorem batchBitOffset_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchBitOffset) s fun t =>
      t.gpr .rsi = BitVec.ofNat 64 (16 * j) ∧ Keeps [.rax, .rdx, .rcx, .rsi] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hv : (BitVec.ofNat 64 j).toNat = j := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply WP.of_runBlock
  simp only [batchBitOffset, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hs.rdi, hr, hc, hv,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · change BitVec.ofNat 64 (j * 16) = BitVec.ofNat 64 (16 * j)
    rw [Nat.mul_comm]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem batchTest_ok {s : State} {base : Addr} (hs : Scratch s base)
    (j : Nat) (hj : j < 32) (hc : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 j) :
    WP isa (.block batchTest) s fun t => t.zf = some (decide (j = 0)) ∧ Keeps [.rbx] s t := by
  have hr : InRegions (s.rd ++ s.wr) (off base 56) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base _ (by decide) (by decide)⟩
  have hz : (BitVec.ofNat 64 j == 0) = decide (j = 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    bv_omega_using [hj]
  apply WP.of_runBlock
  simp only [batchTest, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.zf_arithFlags, hs.rdi, hr, hc, BitVec.and_self, hz,
    ite_true, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

end VG.Proof.Ed25519.X86_64
