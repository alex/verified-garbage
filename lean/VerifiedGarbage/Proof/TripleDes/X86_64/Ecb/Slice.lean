import VerifiedGarbage.Proof.TripleDes.X86_64.Ecb.Pre

/-! # Restricting ECB permissions to a consecutive subrange -/

namespace VG.Proof.TripleDes.X86_64.Ecb

open VG VG.X86_64

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .rdi = s.gpr .rdi)
    (buf : s'.gpr .rdx = s.gpr .rdx) (sp : s'.gpr .rsp = s.gpr .rsp)
    (ptr : s'.gpr .rsi = s.gpr .rsi + BitVec.ofNat 64 (8 * i)) : StepPre s' m := by
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨s'.gpr .rsi, 8 * m⟩ ⟨s.gpr .rsi, 8 * n⟩
    rw [ptr]
    exact Offset.sub_base _ (by omega)
  constructor
  · have hc : Covers [keyR s', dataR s' m, bufR s'] [keyR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [dataR s' m, bufR s'] [dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨dataR s n, by simp, 8 * i, ptr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub
  · simpa only [stackR, keyR, sp, key] using hp.stackKey
  · simpa only [stackR, sp] using hp.stackData.sub_right sub
  · simpa only [stackR, bufR, sp, buf] using hp.stackBuf

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn rfl rfl rfl rfl rfl (by simp)

end VG.Proof.TripleDes.X86_64.Ecb
