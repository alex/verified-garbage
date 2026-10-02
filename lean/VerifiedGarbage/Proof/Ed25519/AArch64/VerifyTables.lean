import VerifiedGarbage.Impl.Ed25519.AArch64.Verify
import VerifiedGarbage.Proof.Ed25519.AArch64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.AArch64.PointAccumulate

/-! Store and reload verification points beyond the multiplication workspace. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


theorem tableIndexZero_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0]) s fun t => t.gpr .x19 = 0 ∧ Keeps [.x19] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, ite_true,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem pointTableWrite_ok {s : State} {base : Addr} (hs : Scr s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep base o 128 s t ∧
      tablePoint t.mem base o = point (env s.mem base) 0 1 2 3 ∧ env t.mem base = env s.mem base := by
  rw [pointTableWrite, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kap : PowersKeep base o 128 s a := PowersKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kap.scratch hs).x0 o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbp : PowersKeep base o 128 a b := PowersKeep.of_keeps kb (by decide)
  refine WP.mono (pointToTable_ok ((kap.trans kbp).scratch hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  have ktp : PowersKeep base o 128 b t := ⟨fun r _ _ hr => kt.gpr r (fun hm => hr (by
    exact (show ∀ r ∈ [Reg.x4, .x5, .x6, .x7], r ∈ clob by decide) r hm)),
    kt.rd, kt.wr, kt.sp, TableFrame.table kt.mem⟩
  refine ⟨(kap.trans kbp).trans ktp, ?_, ?_⟩
  · rw [tp, kb.mem, ka.mem]
  · rw [table_env kt.mem hlo, kb.mem, ka.mem]

theorem pointTableRead_ok {s : State} {base : Addr} (hs : Scr s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => CounterKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [pointTableRead, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kar : CounterKeep base s a := CounterKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scr hs).x0 o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbr : CounterKeep base a b := CounterKeep.of_keeps kb (by decide)
  refine WP.mono (pointFromTable_ok ((kar.trans kbr).scr hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  refine ⟨(kar.trans kbr).trans (CounterKeep.of_keep (Keep.of_table kt)), ?_, ?_⟩
  · rw [tp, kb.mem, ka.mem]
  · intro i hi
    rw [tableLoad_high kt i hi, kb.mem, ka.mem]

end VG.Proof.Ed25519.AArch64
