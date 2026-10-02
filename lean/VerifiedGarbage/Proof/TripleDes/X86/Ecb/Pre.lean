import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Call

/-! # Permissions and separation for one ECB step -/

namespace VG.Proof.TripleDes.X86.Ecb

open VG VG.X86
open VG.Proof.Rc2.X86 (addr32 addr_add)

abbrev keyR (s : State) : Region := ⟨addr32 (s.gpr .ebx), 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨addr32 (s.gpr .esi), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨addr32 (s.gpr .ebp), 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  keyFit : (s.gpr .ebx).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .esi).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .ebp).toNat + 1024 ≤ 2 ^ 32
  stackLo : 16 ≤ (s.gpr .esp).toNat
  stackKey : (below (s.gpr .esp) 16).Disjoint (keyR s)
  stackData : (below (s.gpr .esp) 16).Disjoint (dataR s n)
  stackBuf : (below (s.gpr .esp) 16).Disjoint (bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .ebx (by decide)
  have c := regs .esi (by decide)
  have d := regs .ebp (by decide)
  have sp := regs .esp (by decide)
  constructor
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.reads
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.writes
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyData
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyBuf
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.dataBuf
  · simpa only [a] using hp.keyFit
  · simpa only [c] using hp.dataFit
  · simpa only [d] using hp.bufFit
  · rw [sp]; exact hp.stackLo
  · simpa only [keyR, sp, a] using hp.stackKey
  · simpa only [dataR, sp, c] using hp.stackData
  · simpa only [bufR, sp, d] using hp.stackBuf

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨addr32 (s.gpr .ebx), 384⟩, ⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩]
        [keyR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨addr32 (s.gpr .esi), 8⟩, ⟨addr32 (s.gpr .ebp), 512⟩] [dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.keyFit
  · exact hp.dataFit
  · omega_using [hp.bufFit]
  · exact hp.stackLo
  · exact hp.stackKey
  · exact hp.stackData
  · exact hp.stackBuf.sub_right (Region.sub_prefix (by decide))


end VG.Proof.TripleDes.X86.Ecb
