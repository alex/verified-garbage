import VerifiedGarbage.Proof.Rc2.AArch64.Cbc.Steps

/-! # Permissions and separation for one CBC step -/

namespace VG.Proof.Rc2.AArch64.Cbc

open VG VG.AArch64

abbrev keyR (s : State) : Region := ⟨s.gpr .x0, 128⟩
abbrev ivR (s : State) : Region := ⟨s.gpr .x23, 8⟩
abbrev dataR (s : State) (n : Nat := 1) : Region := ⟨s.gpr .x1, 8 * n⟩
abbrev bufR (s : State) : Region := ⟨s.gpr .x2, 512⟩

structure StepPre (s : State) (n : Nat := 1) : Prop where
  reads : Covers [keyR s, ivR s, dataR s n, bufR s] (s.rd ++ s.wr)
  writes : Covers [ivR s, dataR s n, bufR s] s.wr
  keyIv : (keyR s).Disjoint (ivR s)
  keyData : (keyR s).Disjoint (dataR s n)
  keyBuf : (keyR s).Disjoint (bufR s)
  ivData : (ivR s).Disjoint (dataR s n)
  ivBuf : (ivR s).Disjoint (bufR s)
  dataBuf : (dataR s n).Disjoint (bufR s)

theorem StepPre.transport {s s' : State} {n : Nat} (hp : StepPre s n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr) (regs : ∀ r ∈ kept, s'.gpr r = s.gpr r) : StepPre s' n := by
  have a := regs .x0 (by decide)
  have b := regs .x23 (by decide)
  have c := regs .x1 (by decide)
  have d := regs .x2 (by decide)
  constructor
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.reads
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.writes
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyIv
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyData
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.keyBuf
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.ivData
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.ivBuf
  · simpa only [keyR, ivR, dataR, bufR, rd, wr, a, b, c, d] using hp.dataBuf

theorem StepPre.keep {s s' : State} {m : Mem} {n : Nat} (hp : StepPre s n) (h : Keep [.x8, .x9] {s with mem := m} s') : StepPre s' n :=
  hp.transport h.rd h.wr fun r hr => h.reg r (by
    have sep : ∀ r ∈ kept, r ∉ [.x8, .x9] := by decide
    exact sep r hr)

theorem StepPre.call {s : State} (hp : StepPre s) : CallPre s := by
  constructor
  · have hc : Covers [⟨s.gpr .x0, 128⟩, ⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩]
        [keyR s, ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp, by simp⟩
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.reads a n (hc a n h)
  · have hc : Covers [⟨s.gpr .x1, 8⟩, ⟨s.gpr .x2, 256⟩] [ivR s, dataR s, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s, by simp, 0, by simp, by simp⟩
      · exact ⟨bufR s, by simp, 0, by simp, by simp⟩
    exact fun a n h => hp.writes a n (hc a n h)
  · exact hp.keyBuf.sub_right (Region.sub_prefix (by decide))
  · exact hp.dataBuf.sub_right (Region.sub_prefix (by decide))

theorem StepPre.readData {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .x1) 8 :=
  hp.reads _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readIv {s : State} (hp : StepPre s) : InRegions (s.rd ++ s.wr) (s.gpr .x23) 8 :=
  hp.reads _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeData {s : State} (hp : StepPre s) : InRegions s.wr (s.gpr .x1) 8 :=
  hp.writes _ _ ⟨dataR s, by simp, Region.contains_self _ _⟩

theorem StepPre.writeIv {s : State} (hp : StepPre s) : InRegions s.wr (s.gpr .x23) 8 :=
  hp.writes _ _ ⟨ivR s, by simp, Region.contains_self _ _⟩

theorem StepPre.readBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions (s.rd ++ s.wr) (s.gpr .x2 + BitVec.ofNat 64 i) 8 :=
  hp.reads _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

theorem StepPre.writeBuf {s : State} (hp : StepPre s) (i : Nat) (hi : i + 8 ≤ 512) :
    InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 i) 8 :=
  hp.writes _ _ ⟨bufR s, by simp, Offset.contains_base _ hi (by omega)⟩

end VG.Proof.Rc2.AArch64.Cbc
