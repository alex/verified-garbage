import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch

/-! Untrusted: store and reload verification points beyond the multiplication workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (Keeps clob)

theorem tableIndexZero_ok (s : State) :
    WP isa (.block [.movImm64 .rbx 0]) s fun t => t.gpr .rbx = 0 ∧ Keeps [.rbx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  exact RegUpd.gpr_setReg_of_ne _ _ (by simpa only [List.mem_singleton] using hr)

theorem pointTableWrite_ok {s : State} {base : Addr} (hs : Scratch s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableWrite o)) s fun t => PowersKeep base o 128 s t ∧
      tablePoint t.mem base o = point (env s.mem base) 0 1 2 3 ∧ env t.mem base = env s.mem base := by
  rw [pointTableWrite, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kap : PowersKeep base o 128 s a := PowersKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kap.scratch hs).rdi o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbp : PowersKeep base o 128 a b := PowersKeep.of_keeps kb (by decide)
  refine WP.mono (pointToTable_ok ((kap.trans kbp).scratch hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  have ktp : PowersKeep base o 128 b t := ⟨fun r _ _ hr => kt.gpr r (fun hm => hr (by
    exact (show ∀ r ∈ [Reg.r8, .r9, .r10, .r11], r ∈ clob by decide) r hm)),
    kt.rd, kt.wr, TableFrame.table kt.mem⟩
  refine ⟨(kap.trans kbp).trans ktp, ?_, ?_⟩
  · rw [tp, kb.2.1, ka.2.1]
  · rw [table_env kt.mem hlo, kb.2.1, ka.2.1]

theorem pointTableRead_ok {s : State} {base : Addr} (hs : Scratch s base)
    (o : Nat) (hlo : 768 ≤ o) (ho : o + 128 ≤ 8192) :
    WP isa (.block (pointTableRead o)) s fun t => RbxKeep base s t ∧
      point (env t.mem base) 0 1 2 3 = tablePoint s.mem base o ∧
      ∀ i : Slot, 4 ≤ i.val → env t.mem base i = env s.mem base i := by
  rw [pointTableRead, List.append_assoc, WP.block_append_iff]
  refine WP.mono (tableIndexZero_ok s) fun a ⟨az, ka⟩ => ?_
  have kar : RbxKeep base s a := RbxKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (tableAddr_ok (kar.scratch hs).rdi o 0 (by decide) az) fun b ⟨bp, kb⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at bp
  have kbr : RbxKeep base a b := RbxKeep.of_keeps kb (by decide)
  refine WP.mono (pointFromTable_ok ((kar.trans kbr).scratch hs) bp hlo ho) fun t ⟨tp, kt⟩ => ?_
  refine ⟨(kar.trans kbr).trans (RbxKeep.of_keep (Keep.of_table kt)), ?_, ?_⟩
  · rw [tp, kb.2.1, ka.2.1]
  · intro i hi
    rw [tableLoad_high kt i hi, kb.2.1, ka.2.1]

end VG.Proof.Ed25519.X86_64
