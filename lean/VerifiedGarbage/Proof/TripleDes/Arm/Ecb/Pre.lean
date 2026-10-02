import VerifiedGarbage.Proof.TripleDes.Arm.Ecb.Call

/-! # Permissions and separation for one ECB step -/

namespace VG.Proof.TripleDes.Arm.Ecb

open VG VG.Arm

abbrev keyR (s : State) : Region := ⟨State.addr (s.gpr .r0), 384⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨State.addr (s.gpr .r1), 8 * n⟩
abbrev bufR (s : State) : Region := ⟨State.addr (s.gpr .r2), 1024⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [dataR s n, bufR s] s.wr
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)
  keyFit : (s.gpr .r0).toNat + 384 ≤ 2 ^ 32
  dataFit : (s.gpr .r1).toNat + 8 * n ≤ 2 ^ 32
  bufFit : (s.gpr .r2).toNat + 1024 ≤ 2 ^ 32

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .r0 (by decide)
  have c := regs .r1 (by decide)
  have d := regs .r2 (by decide)
  constructor
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.reads
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.writes
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyData
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.keyBuf
  · simpa only [keyR, dataR, bufR, rd, wr, a, c, d] using hp.dataBuf
  · simpa only [a] using hp.keyFit
  · simpa only [c] using hp.dataFit
  · simpa only [d] using hp.bufFit

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨State.addr (s.gpr .r0), 384⟩, ⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩]
        [keyR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨State.addr (s.gpr .r1), 8⟩, ⟨State.addr (s.gpr .r2), 512⟩] [dataR s, bufR s] := by
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


end VG.Proof.TripleDes.Arm.Ecb
