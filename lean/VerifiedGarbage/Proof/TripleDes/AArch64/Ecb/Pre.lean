import VerifiedGarbage.Proof.TripleDes.AArch64.Ecb.Call

/-! # Permissions and separation for one ECB step -/

namespace VG.Proof.TripleDes.AArch64.Ecb

open VG VG.AArch64

abbrev keyR (s : State) : Region := ⟨s.gpr .x0, 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨s.gpr .x1, 8 * n⟩
abbrev bufR (s : State) : Region := ⟨s.gpr .x2, 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .x0 (by decide)
  have c := regs .x1 (by decide)
  have d := regs .x2 (by decide)
  constructor
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.reads
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.writes
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyData
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyBuf
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.dataBuf

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨s.gpr .x0, 384⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩]
        [keyR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 512⟩] [dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))


end VG.Proof.TripleDes.AArch64.Ecb
