import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Frame

/-! # Restricting CBC permissions to a consecutive subrange -/

namespace VG.Proof.Rc2.Arm.Cbc

open VG VG.Arm

theorem StepPre.slice {s s' : State} {n m i : Nat} (hp : StepPre s n) (bound : i + m ≤ n)
    (startFit : (s.gpr .r1).toNat + 8 * i < 2 ^ 32)
    (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
    (key : s'.gpr .r0 = s.gpr .r0) (iv : s'.gpr .r4 = s.gpr .r4)
    (buf : s'.gpr .r2 = s.gpr .r2)
    (ptr : s'.gpr .r1 = s.gpr .r1 + BitVec.ofNat 32 (8 * i)) : StepPre s' m := by
  have ptrAddr : State.addr (s'.gpr .r1) = State.addr (s.gpr .r1) + BitVec.ofNat 64 (8 * i) := by
    rw [ptr]; exact addr_add startFit
  have fit : (s'.gpr .r1).toNat + 8 * m ≤ 2 ^ 32 := by
    rw [ptr, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
      Nat.mod_eq_of_lt startFit]
    have := hp.dataFit
    omega
  have sub : Region.Sub (dataR s' m) (dataR s n) := by
    change Region.Sub ⟨State.addr (s'.gpr .r1), 8 * m⟩ ⟨State.addr (s.gpr .r1), 8 * n⟩
    rw [ptrAddr]
    exact Offset.sub_base _ (by omega)
  constructor
  · rw [key]; exact hp.keyFit
  · rw [iv]; exact hp.ivFit
  · exact fit
  · rw [buf]; exact hp.bufFit
  · have hc : Covers [keyR s', ivR s', dataR s' m, bufR s'] [keyR s, ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact ⟨keyR s, by simp, 0, by simp [key], by simp⟩
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [rd, wr]
    exact fun a k h => hp.reads a k (hc a k h)
  · have hc : Covers [ivR s', dataR s' m, bufR s'] [ivR s, dataR s n, bufR s] := by
      apply Covers.of_sub
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨ivR s, by simp, 0, by simp [iv], by simp⟩
      · exact ⟨dataR s n, by simp, 8 * i, ptrAddr, by change 8 * i + 8 * m ≤ 8 * n; omega⟩
      · exact ⟨bufR s, by simp, 0, by simp [buf], by simp⟩
    rw [wr]
    exact fun a k h => hp.writes a k (hc a k h)
  · simpa only [keyR, ivR, key, iv] using hp.keyIv
  · simpa only [keyR, key] using hp.keyData.sub_right sub
  · simpa only [keyR, bufR, key, buf] using hp.keyBuf
  · simpa only [ivR, iv] using hp.ivData.sub_right sub
  · simpa only [ivR, bufR, iv, buf] using hp.ivBuf
  · simpa only [bufR, buf] using hp.dataBuf.sub_left sub

theorem StepPre.head {s : State} {n : Nat} (hp : StepPre s n) (hn : 1 ≤ n) : StepPre s :=
  hp.slice (i := 0) hn (by simpa using (s.gpr .r1).isLt) rfl rfl rfl rfl rfl (by simp)

end VG.Proof.Rc2.Arm.Cbc
